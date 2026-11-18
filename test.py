#!/usr/bin/env python

"""Test suite for cloud.py - stdlib only, run with `python test.py`"""

import subprocess
import unittest
from asyncio import run as asyncio_run
from contextlib import redirect_stdout
from hashlib import sha1
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import AsyncMock, patch

import cloud
from cloud import CloudException, OVHApi, OVHConfig, ScalewayConfig, atomic_write, confirm, ovh_orders

PIN_COMMAND = ("/bin/echo", "0" * 64)  # a certificate is configured as a command that prints its pins

INJECTION_SHAPED_INPUTS = [
    "../../../etc/passwd",
    "id/../admin",
    "id?admin=true",
    "id&key=value",
    "id;rm -rf .",
    "id id",
    "id%0aheader",
    "id\ninjected",
    "id#fragment",
    'id"quoted"',
]


def make_ovh_api():
    return OVHApi(
        pin_command=PIN_COMMAND,
        pdf_pin_command=("/bin/echo", "1" * 64),
        application_key="fake-application-key",
        application_secret="fake-application-secret",
        consumer_key="fake-consumer-key",
        cafile="/nonexistent/cacert.pem",
    )


class TestValidators(unittest.TestCase):
    """The _validate_* allowlists must accept legitimate ids and reject anything injection-shaped"""

    def setUp(self):
        self.api = make_ovh_api()

    def check(self, validator, valid_inputs, extra_invalid_inputs=()):
        for valid_input in valid_inputs:
            validator(valid_input)  # Must not raise
        for invalid_input in (*INJECTION_SHAPED_INPUTS, *extra_invalid_inputs):
            with self.assertRaises(CloudException, msg=f"{validator.__name__} accepted {invalid_input!r}"):
                validator(invalid_input)

    def test_validate_vps_id(self):
        self.check(self.api._validate_vps_id, ["vps-12345678.vps.ovh.net"], ["VPS-UPPER", "vps_underscore"])

    def test_validate_server_id(self):
        self.check(self.api._validate_server_id, ["ns1234567.ip-1-2-3.eu"], ["NS.UPPER", "ns_underscore"])

    def test_validate_domain(self):
        self.check(self.api._validate_domain, ["example.ovh", "sub.Example.com"], ["exa mple.com", "domainé.fr"])

    def test_validate_record_id(self):
        self.check(self.api._validate_record_id, ["1234567", 1234567], ["12_34"])

    def test_validate_cart_id(self):
        self.check(self.api._validate_cart_id, ["0a1b2c3d-4e5f-6789-abcd-ef0123456789"], ["ABCDEF", "abc_def"])

    def test_validate_email_domain_name(self):
        self.check(self.api._validate_email_domain_name, ["example.ovh"], ["EXAMPLE.OVH", "exam_ple.ovh"])

    def test_validate_email_account_name(self):
        self.check(self.api._validate_email_account_name, ["john.doe", "john_doe-2"], ["JOHN", "john@doe"])

    def test_validate_billing_account(self):
        self.check(self.api._validate_billing_account, ["ovhtel-12345-1.fr"], ["OVHTEL", "tel_account"])

    def test_validate_service_name(self):
        self.check(self.api._validate_service_name, ["0033123456789"], ["0033_1234", "SERVICE"])

    def test_validate_order_id(self):
        self.check(self.api._validate_order_id, ["123456789", 123456789], ["12a34", "-1", "1.5"])


class TestConfirm(unittest.TestCase):
    """confirm() only accepts a literal YES, anything else raises CloudException"""

    def test_yes_passes(self):
        with patch("builtins.input", return_value="YES"):
            confirm("Dangerous operation. ")  # Must not raise

    def test_anything_else_raises(self):
        for answer in ["yes", "Yes", "NO", "no", "", "Y", " YES", "YES ", "y"]:
            with patch("builtins.input", return_value=answer):
                with self.assertRaises(CloudException, msg=f"confirm accepted {answer!r}"):
                    confirm("Dangerous operation. ")


class TestOvhOrdersPay(unittest.TestCase):
    """`cloud ovh orders pay` must show the order and require a confirm() before charging anything"""

    def make_api_mock(self):
        api = AsyncMock()
        api.get_order.return_value = {"orderId": 123456789, "priceWithTax": {"text": "12.34 €", "value": 12.34}}
        return api

    def test_pay_is_not_called_without_confirmation(self):
        api = self.make_api_mock()
        with patch("builtins.input", return_value="no"), redirect_stdout(StringIO()):
            with self.assertRaises(CloudException):
                asyncio_run(ovh_orders(api, ["pay", "123456789", "1"]))
        api.get_order.assert_awaited_once_with("123456789")
        api.pay_order.assert_not_called()

    def test_pay_is_called_after_confirmation(self):
        api = self.make_api_mock()
        with patch("builtins.input", return_value="YES"), redirect_stdout(StringIO()):
            asyncio_run(ovh_orders(api, ["pay", "123456789", "1"]))
        api.pay_order.assert_awaited_once_with(order_id="123456789", payment_method_id="1")

    def test_confirm_message_includes_order_id_and_price(self):
        api = self.make_api_mock()
        seen_prompts = []

        def fake_input(prompt):
            seen_prompts.append(prompt)
            return "no"

        with patch("builtins.input", fake_input), redirect_stdout(StringIO()):
            with self.assertRaises(CloudException):
                asyncio_run(ovh_orders(api, ["pay", "123456789", "1"]))
        self.assertEqual(len(seen_prompts), 1)
        self.assertIn("123456789", seen_prompts[0])
        self.assertIn("12.34 €", seen_prompts[0])


class TestOVHSignature(unittest.TestCase):
    """The OVH request signature must be '$1$' + sha1(secret+consumer+METHOD+query+body+timestamp)"""

    def test_calculate_signature_known_inputs(self):
        api = make_ovh_api()
        query, body, timestamp = "https://eu.api.ovh.com/1.0/me", "", 1700000000
        expected_data = f"fake-application-secret+fake-consumer-key+GET+{query}+{body}+{timestamp}"
        expected = "$1$" + sha1(expected_data.encode("utf-8")).hexdigest()
        self.assertEqual(api._calculate_signature("GET", query, body, timestamp), expected)

    def test_make_request_signs_with_frozen_time(self):
        api = make_ovh_api()
        captured = {}

        async def fake_make_request(pin_command, method, query, body, headers, **kwargs):
            captured.update(pin_command=pin_command, method=method, query=query, body=body, headers=headers, **kwargs)
            return {}

        with patch("cloud.time_time", return_value=1700000000.5), patch("cloud.make_request", fake_make_request):
            asyncio_run(api._make_request("POST", "/me/order/1/payWithRegisteredPaymentMean", {"a": "b"}))
        expected_data = (
            "fake-application-secret+fake-consumer-key+POST"
            '+https://eu.api.ovh.com/1.0/me/order/1/payWithRegisteredPaymentMean+{"a": "b"}+1700000000'
        )
        expected = "$1$" + sha1(expected_data.encode("utf-8")).hexdigest()
        self.assertEqual(captured["headers"]["X-Ovh-Timestamp"], "1700000000")
        self.assertEqual(captured["headers"]["X-Ovh-Signature"], expected)
        self.assertEqual(captured["pin_command"], PIN_COMMAND)
        self.assertEqual(captured["cafile"], "/nonexistent/cacert.pem")


class TestAtomicWrite(unittest.TestCase):
    """atomic_write leaves the path complete or untouched, and no temp file behind that goes unnoticed"""

    def setUp(self):
        directory = TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.path = Path(directory.name) / "voicemail.wav"
        self.tmp_path = Path(directory.name) / "voicemail.wav.tmp"

    def files(self):
        return [path.name for path in self.path.parent.iterdir()]

    def test_writes_and_replaces(self):
        self.path.write_bytes(b"old")
        atomic_write(self.path, b"new" * 100000)
        self.assertEqual(self.path.read_bytes(), b"new" * 100000)
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)
        self.assertEqual(self.files(), ["voicemail.wav"])

    def test_failed_write_leaves_the_path_untouched_and_no_temp_file(self):
        self.path.write_bytes(b"old")
        with self.assertRaises(TypeError):
            atomic_write(self.path, "not bytes")
        self.assertEqual(self.path.read_bytes(), b"old")
        self.assertEqual(self.files(), ["voicemail.wav"])

    def test_failed_replace_removes_the_temp_file(self):
        with patch.object(Path, "replace", side_effect=OSError("no rename today")), self.assertRaises(OSError):
            atomic_write(self.path, b"new")
        self.assertEqual(self.files(), [])

    def test_failed_cleanup_shows_both_errors(self):
        """Nothing is swallowed: the cleanup error is raised, with what caused the cleanup as its context"""
        with (
            patch.object(Path, "replace", side_effect=OSError("no rename today")),
            patch.object(Path, "unlink", side_effect=OSError("no unlink either")),
            self.assertRaises(OSError) as ctx,
        ):
            atomic_write(self.path, b"new")
        self.assertEqual(str(ctx.exception), "no unlink either")
        self.assertEqual(str(ctx.exception.__context__), "no rename today")
        self.assertFalse(self.path.exists())

    def test_existing_temp_file_is_refused_and_kept(self):
        """It is the lock of a run in progress, or what a killed one left: never overwritten, never removed"""
        self.path.write_bytes(b"old")
        self.tmp_path.write_bytes(b"leftover")
        with self.assertRaises(CloudException) as ctx:
            atomic_write(self.path, b"new")
        self.assertIn(str(self.tmp_path), str(ctx.exception))
        self.assertEqual(self.path.read_bytes(), b"old")
        self.assertEqual(self.tmp_path.read_bytes(), b"leftover")


class TestConfig(unittest.TestCase):
    """Certificates are configured as commands, validated when the config is loaded and not run then"""

    OVH = {"application-key": "k", "application-secret": "s", "consumer-key": "c"}
    SCALEWAY = {"secret-key": "s", "organization-id": "o"}

    def test_config_accepts_commands(self):
        command, pdf_command = ["/nonexistent/tls-pin-get", "eu.api.ovh.com:443"], ["/bin/echo", "a" * 64]
        ovh_config = OVHConfig({**self.OVH, "certificate": command, "pdf-certificate": pdf_command})
        self.assertEqual(ovh_config.certificate, tuple(command))
        self.assertEqual(ovh_config.pdf_certificate, tuple(pdf_command))
        self.assertEqual(ScalewayConfig({**self.SCALEWAY, "certificate": command}).certificate, tuple(command))

    def test_config_rejects_what_is_not_a_command(self):
        """A hash, as it used to be, included"""
        for value, name in ((123, "int"), ("a" * 64, "str"), ({"command": ["cmd"]}, "dict"), (None, "NoneType")):
            with self.subTest(value=value):
                with self.assertRaises(CloudException) as ctx:
                    ScalewayConfig({**self.SCALEWAY, "certificate": value})
                expected = f"Scaleway certificate must be a command (list of strings), got {name}"
                self.assertEqual(str(ctx.exception), expected)
                with self.assertRaises(CloudException) as ctx:
                    OVHConfig({**self.OVH, "certificate": ["cmd"], "pdf-certificate": value})
                expected = f"OVH pdf-certificate must be a command (list of strings), got {name}"
                self.assertEqual(str(ctx.exception), expected)

    def test_config_rejects_bad_commands(self):
        for command in ([], [""], ["cmd", 1], ["cmd", ["nested"]], ["cmd", "a\0b"]):
            with self.subTest(command=command), self.assertRaises(CloudException) as ctx:
                ScalewayConfig({**self.SCALEWAY, "certificate": command})
            expected = "Scaleway certificate command must be a non-empty list of non-empty strings"
            self.assertEqual(str(ctx.exception), expected)

    def test_cafile_is_required(self):
        for config in ("{}", '{"ssl-cafile": ""}', '{"ssl-cafile": null}', '{"ssl-cafile": ["/ca.pem"]}'):
            with self.subTest(config=config), patch.object(Path, "open", return_value=StringIO(config)):
                with self.assertRaises(CloudException) as ctx:
                    cloud.load_config()
                self.assertEqual(str(ctx.exception), "Missing or invalid 'ssl-cafile' in config")


class TestPinCommand(unittest.TestCase):
    """A certificate is configured as a command that prints the SHA256 pins to accept"""

    @staticmethod
    def sh(script):
        return ("/bin/sh", "-c", script)

    @staticmethod
    def request(pin_command):
        return asyncio_run(cloud.make_request(pin_command, "GET", "https://cloud.example/", "", {}, cafile="/ca.pem"))

    def test_static_pin(self):
        """A hash that never changes is still possible: echo"""
        self.assertEqual(cloud.resolve_pins(("/bin/echo", "a" * 64)), ("a" * 64,))

    def test_command_several_pins(self):
        """All of them are accepted: the old and the new certificate overlap during a rotation"""
        pins = cloud.resolve_pins(self.sh(f"printf '%s\\n' {'a' * 64} {'B' * 64}"))
        self.assertEqual(pins, ("a" * 64, "b" * 64))

    def test_command_receives_arguments_without_a_shell(self):
        with patch("cloud.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, stdout=b"c" * 64 + b"\n", stderr=b"")
            self.assertEqual(cloud.resolve_pins(("tls-pin-get", "host; rm -rf $HOME")), ("c" * 64,))
        self.assertEqual(mock_run.call_args.args, (("tls-pin-get", "host; rm -rf $HOME"),))
        self.assertNotIn("shell", mock_run.call_args.kwargs)

    def test_command_is_run_once(self):
        with patch("cloud.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, stdout=b"d" * 64 + b"\n", stderr=b"")
            cloud.resolve_pins(("tls-pin-get", "run-once.example:443"))
            cloud.resolve_pins(("tls-pin-get", "run-once.example:443"))
        self.assertEqual(mock_run.call_count, 1)

    def test_command_failures(self):
        cases = {
            "exit 1": "Pin command failed (exit code 1): /bin/sh -c exit 1",
            "echo 'no pin for x' >&2; exit 1": (
                "Pin command failed (exit code 1): /bin/sh -c echo 'no pin for x' >&2; exit 1: no pin for x"
            ),
            f"echo {'a' * 64}; exit 3": f"Pin command failed (exit code 3): /bin/sh -c echo {'a' * 64}; exit 3",
            "true": "Pin command printed no pin: /bin/sh -c true",
            "echo": "Pin command printed no pin: /bin/sh -c echo",
        }
        for script, expected in cases.items():
            with self.subTest(script=script), self.assertRaises(CloudException) as ctx:
                cloud.resolve_pins(self.sh(script))
            self.assertEqual(str(ctx.exception), expected)

    def test_command_output_that_is_not_pins(self):
        scripts = [
            "echo not-a-pin",
            f"echo {'a' * 63}",
            f"echo {'a' * 65}",
            f"echo {'g' * 64}",
            f"echo ' {'a' * 64}'",
            f"echo {'a' * 64}; echo",
            f"echo {'a' * 64}; echo not-a-pin",
            f"printf '\\351%s\\n' {'a' * 63}",
        ]
        for script in scripts:
            with self.subTest(script=script), self.assertRaises(CloudException) as ctx:
                cloud.resolve_pins(self.sh(script))
            self.assertIn("Pin command printed something that is not a SHA256", str(ctx.exception))

    def test_command_too_many_pins(self):
        with self.assertRaises(CloudException) as ctx:
            cloud.resolve_pins(self.sh(f"for i in $(seq 17); do echo {'a' * 64}; done"))
        self.assertIn("Pin command printed more than 16 pins", str(ctx.exception))

    def test_command_not_found(self):
        with self.assertRaises(CloudException) as ctx:
            cloud.resolve_pins(("/nonexistent/tls-pin-get", "eu.api.ovh.com:443"))
        self.assertIn("Pin command could not be run: /nonexistent/tls-pin-get eu.api.ovh.com:443", str(ctx.exception))

    def test_command_timeout(self):
        with patch("cloud.subprocess.run", side_effect=subprocess.TimeoutExpired("cmd", 10)):
            with self.assertRaises(CloudException) as ctx:
                cloud.resolve_pins(("tls-pin-get", "timeout.example:443"))
        self.assertEqual(str(ctx.exception), "Pin command timed out after 10s: tls-pin-get timeout.example:443")

    def test_failing_command_means_no_connection(self):
        """And with what went wrong: not as an unknown error"""
        with patch("cloud.urllib.request.urlopen") as mock_urlopen:
            with self.assertRaises(CloudException) as ctx:
                self.request(self.sh("exit 1"))
        mock_urlopen.assert_not_called()
        self.assertEqual(str(ctx.exception), "Pin command failed (exit code 1): /bin/sh -c exit 1")

    def test_resolved_pins_reach_the_ssl_context(self):
        with (
            patch.object(cloud, "make_pinned_ssl_context") as mock_context,
            patch("cloud.urllib.request.urlopen") as mock_urlopen,
        ):
            mock_urlopen.return_value.read.return_value = b'{"ok": true}'
            self.assertEqual(self.request(self.sh(f"echo {'a' * 64}; echo {'b' * 64}")), {"ok": True})
        mock_context.assert_called_once_with(("a" * 64, "b" * 64), cafile="/ca.pem")
        self.assertIs(mock_urlopen.call_args.kwargs["context"], mock_context.return_value)

    def test_cafile_can_not_be_forgotten(self):
        with self.assertRaises(TypeError):
            asyncio_run(cloud.make_request(PIN_COMMAND, "GET", "https://x.example/", "", {}))  # ty: ignore[missing-argument]

    def test_pinned_context_accepts_one_or_several_pins(self):
        for pins in ("a" * 64, ("a" * 64, "b" * 64), []):
            with self.subTest(pins=pins):
                context = cloud.make_pinned_ssl_context(pins)
                self.assertTrue(context.check_hostname)


if __name__ == "__main__":
    unittest.main(verbosity=2)
