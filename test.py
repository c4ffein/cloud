#!/usr/bin/env python

"""Test suite for cloud.py - stdlib only, run with `python test.py`"""

import os
import ssl
import subprocess
import unittest
import urllib.request
from asyncio import run as asyncio_run
from contextlib import redirect_stdout
from hashlib import sha1
from http.server import BaseHTTPRequestHandler, HTTPServer
from io import BytesIO, StringIO
from json import dumps
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Thread
from unittest.mock import AsyncMock, patch
from urllib.error import HTTPError

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
# What an allowlist of chars alone lets through: nothing, the dot segments of a URL, and what is not even a str
NOT_IDS = ["", ".", "..", ".hidden", ["ab", "12"], ("a",), {"a": 1}, None, b"id", 1.5, True]


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
        for invalid_input in (*INJECTION_SHAPED_INPUTS, *NOT_IDS, *extra_invalid_inputs):
            with self.assertRaises(CloudException, msg=f"{validator.__name__} accepted {invalid_input!r}"):
                validator(invalid_input)

    def test_is_valid_id(self):
        for value in ("a", "abc", "a.b", "a..b", "ab."):
            self.assertTrue(cloud.is_valid_id(value, "abc."), msg=value)
        for value in (*NOT_IDS, "abd", "a b", "a/b", 12):
            self.assertFalse(cloud.is_valid_id(value, "abc."), msg=repr(value))

    def test_ids_from_the_server_are_validated_too(self):
        """What a list answers is what the next URLs are built with"""
        listings = [
            (self.api.list_vps, "/vps"),
            (self.api.list_server, "/dedicated/server"),
            (self.api.list_invoices, "/me/bill"),
            (self.api.list_ssh_keys, "/me/sshKey"),
            (self.api.list_telephony_services, "/telephony"),
            (self.api.list_orders, "/me/order"),
        ]
        for listing, path in listings:
            for answer in ([".."], [""], [["1", "2"]], ["1", "../1"]):
                requests = []

                async def fake_make_request(
                    pin_command, method, query, *args, answer=answer, requests=requests, **kwargs
                ):
                    requests.append(query)
                    return answer

                with self.subTest(path=path, answer=answer), patch("cloud.make_request", fake_make_request):
                    with self.assertRaises(CloudException):
                        asyncio_run(listing())
                    self.assertEqual(
                        requests, [f"https://eu.api.ovh.com/1.0{path}"]
                    )  # and nothing built from the answer

    def test_validate_vps_id(self):
        self.check(self.api._validate_vps_id, ["vps-12345678.vps.ovh.net"], ["VPS-UPPER", "vps_underscore"])

    def test_validate_server_id(self):
        self.check(self.api._validate_server_id, ["ns1234567.ip-1-2-3.eu"], ["NS.UPPER", "ns_underscore"])

    def test_validate_domain(self):
        valid = ["example.ovh", "sub.Example.com", "my-site.ovh"]
        self.check(self.api._validate_domain, valid, ["exa mple.com", "domainé.fr", "exa_mple.com"])

    def test_validate_ssh_key(self):
        """Not checked against INJECTION_SHAPED_INPUTS: a key goes in a JSON body, and needs / and spaces"""
        base64_part = "AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GK+/"
        for key in (
            f"ssh-ed25519 {base64_part} me@host",
            f"ssh-rsa {base64_part}== first_last@my-laptop.local",
            f"sk-ssh-ed25519@openssh.com {base64_part}",
        ):
            self.api._validate_ssh_key(key)  # Must not raise
        invalid_keys = (
            "",
            None,
            ["ssh-ed25519"],
            "ssh-ed25519 AAAA\nssh-rsa BBBB",
            'key"quoted"',
            "key;rm",
            "clé",
            "a\0b",
        )
        for key in invalid_keys:
            with self.assertRaises(CloudException, msg=f"_validate_ssh_key accepted {key!r}"):
                self.api._validate_ssh_key(key)

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


class TestConfirmedCommands(unittest.TestCase):
    """Commands that destroy something: nothing is called without a YES, and the prompt says what is at stake"""

    CASES = [
        (cloud.ovh_email, ["delete-account", "example.ovh", "jo"], "delete_an_email_account", ("example.ovh", "jo")),
        (cloud.ovh_buy, ["cancel", "0a1b2c3d"], "cancel_cart", ("0a1b2c3d",)),
    ]

    def test_nothing_is_called_without_confirmation(self):
        for handler, args, _, _ in self.CASES:
            api, prompts = AsyncMock(), []
            with self.subTest(args=args), redirect_stdout(StringIO()):
                with patch("builtins.input", lambda prompt, prompts=prompts: prompts.append(prompt) or "yes"):
                    with self.assertRaises(CloudException):
                        asyncio_run(handler(api, args))
                self.assertEqual(api.mock_calls, [])
                self.assertEqual(len(prompts), 1)
                for arg in args[1:]:
                    self.assertIn(arg, prompts[0])

    def test_called_after_confirmation(self):
        for handler, args, method, expected in self.CASES:
            api = AsyncMock()
            with self.subTest(args=args), patch("builtins.input", return_value="YES"), redirect_stdout(StringIO()):
                asyncio_run(handler(api, args))
                getattr(api, method).assert_awaited_once_with(*expected)


class TestVoicemailFileNames(unittest.TestCase):
    """The id in the file name is the one that was parsed and requested, not whatever int() let through"""

    def test_id_is_normalized(self):
        cases = {"download": "voicemail_acc-1_0033123_12.mp3", "download-greeting": "greeting_acc-1_0033123_12.mp3"}
        for typed_id in ("12", " 12\n", "+12", "1_2", "١٢"):
            for verb, expected in cases.items():
                api = AsyncMock()
                api.download_voicemail_message.return_value = api.download_voicemail_greeting.return_value = b"audio"
                with self.subTest(typed_id=typed_id, verb=verb), redirect_stdout(StringIO()):
                    with patch("cloud.atomic_write") as mock_write:
                        asyncio_run(cloud.ovh_telephony(api, ["voicemail", "acc-1", "0033123", typed_id, verb, "mp3"]))
                    mock_write.assert_called_once_with(expected, b"audio")


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

    def test_what_is_read_back_must_be_what_was_written(self):
        self.path.write_bytes(b"old")
        with patch.object(Path, "read_bytes", return_value=b"something else"), self.assertRaises(CloudException) as ctx:
            atomic_write(self.path, b"new")
        self.assertIn(str(self.tmp_path), str(ctx.exception))
        self.assertEqual(self.files(), ["voicemail.wav"])
        with self.path.open("rb") as f:
            self.assertEqual(f.read(), b"old")

    def test_existing_temp_file_is_refused_and_kept(self):
        """It is the lock of a run in progress, or what a killed one left: never overwritten, never removed"""
        self.path.write_bytes(b"old")
        self.tmp_path.write_bytes(b"leftover")
        with self.assertRaises(CloudException) as ctx:
            atomic_write(self.path, b"new")
        self.assertIn(str(self.tmp_path), str(ctx.exception))
        self.assertEqual(self.path.read_bytes(), b"old")
        self.assertEqual(self.tmp_path.read_bytes(), b"leftover")


class TestSaveInvoice(unittest.TestCase):
    """Invoices go through atomic_write: private, never through a symlink, and only when they are PDFs"""

    def setUp(self):
        directory = TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.path = self.directory / "FR123.pdf"

    def save(self, path, content):
        with redirect_stdout(StringIO()):
            cloud.save_invoice(path, content)

    def test_pdf_is_saved_private(self):
        self.save(self.path, b"%PDF-1.4 content")
        self.assertEqual(self.path.read_bytes(), b"%PDF-1.4 content")
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)
        self.assertEqual([path.name for path in self.directory.iterdir()], ["FR123.pdf"])

    def test_what_is_not_a_pdf_is_not_saved(self):
        for content in (b"", b"<html>login</html>", b" %PDF-1.4"):
            with self.subTest(content=content), self.assertRaises(CloudException) as ctx:
                self.save(self.path, content)
            self.assertIn("Not a PDF", str(ctx.exception))
        self.assertEqual(list(self.directory.iterdir()), [])

    def test_missing_directory(self):
        with self.assertRaises(CloudException) as ctx:
            self.save(self.directory / "2026" / "FR123.pdf", b"%PDF-1.4")
        self.assertEqual(str(ctx.exception), f"Directory does not exist: {self.directory / '2026'}")

    def test_symlink_planted_as_the_temp_file_is_not_followed(self):
        victim = self.directory / "victim"
        victim.write_bytes(b"precious")
        (self.directory / "FR123.pdf.tmp").symlink_to(victim)
        with self.assertRaises(CloudException):
            self.save(self.path, b"%PDF-1.4")
        self.assertEqual(victim.read_bytes(), b"precious")
        self.assertFalse(self.path.exists())


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
                    OVHConfig({**self.OVH, "certificate": ["/cmd"], "pdf-certificate": value})
                expected = f"OVH pdf-certificate must be a command (list of strings), got {name}"
                self.assertEqual(str(ctx.exception), expected)

    def test_config_rejects_bad_commands(self):
        for command in ([], [""], ["cmd", 1], ["cmd", ["nested"]], ["cmd", "a\0b"]):
            with self.subTest(command=command), self.assertRaises(CloudException) as ctx:
                ScalewayConfig({**self.SCALEWAY, "certificate": command})
            expected = "Scaleway certificate command must be a non-empty list of non-empty strings"
            self.assertEqual(str(ctx.exception), expected)

    def test_config_rejects_commands_without_a_full_path(self):
        """No PATH lookup, and nothing relative to the directory cloud is run from"""
        for program in ("tls-pin-get", "./tls-pin-get", "bin/tls-pin-get", "~/bin/tls-pin-get"):
            with self.subTest(program=program), self.assertRaises(CloudException) as ctx:
                ScalewayConfig({**self.SCALEWAY, "certificate": [program, "api.scaleway.com:443"]})
            expected = f"Scaleway certificate command must start with a full path, got {program!r}"
            self.assertEqual(str(ctx.exception), expected)

    def load_config(self, content, mode=0o600):
        """cloud.load_config(), with `content` as the config file of a home made for the occasion"""
        home = TemporaryDirectory()
        self.addCleanup(home.cleanup)
        path = Path(home.name) / ".config" / "cloud" / "config.json"
        path.parent.mkdir(parents=True)
        path.write_text(content)
        path.chmod(mode)
        with patch.object(Path, "home", return_value=Path(home.name)):
            return path, cloud.load_config()

    def valid_config(self):
        command = ["/bin/echo", "a" * 64]
        ovh = {**self.OVH, "certificate": command, "pdf-certificate": command}
        return dumps({"ssl-cafile": "/ca.pem", "ovh": ovh, "scaleway": {**self.SCALEWAY, "certificate": command}})

    def test_cafile_is_required(self):
        for config in ("{}", '{"ssl-cafile": ""}', '{"ssl-cafile": null}', '{"ssl-cafile": ["/ca.pem"]}'):
            with self.subTest(config=config), self.assertRaises(CloudException) as ctx:
                self.load_config(config)
            self.assertEqual(str(ctx.exception), "Missing or invalid 'ssl-cafile' in config")

    def test_private_config_is_loaded(self):
        for mode in (0o600, 0o400):
            with self.subTest(mode=oct(mode)):
                _, (ovh_config, scaleway_config, cafile) = self.load_config(self.valid_config(), mode)
                self.assertEqual(ovh_config.certificate, ("/bin/echo", "a" * 64))
                self.assertEqual(scaleway_config.secret_key, "s")
                self.assertEqual(cafile, "/ca.pem")

    def test_config_that_others_can_access_is_refused(self):
        """It holds secrets, and commands that get run"""
        for mode in (0o644, 0o640, 0o620, 0o602, 0o604, 0o660, 0o666, 0o700 | 0o010):
            with self.subTest(mode=oct(mode)), self.assertRaises(CloudException) as ctx:
                self.load_config(self.valid_config(), mode)
            self.assertIn("is accessible by group or others: not used, chmod 600 it", str(ctx.exception))

    def test_config_of_somebody_else_is_refused(self):
        with patch("cloud.os.geteuid", return_value=os.geteuid() + 1), self.assertRaises(CloudException) as ctx:
            self.load_config(self.valid_config())
        self.assertIn("is not owned by you: not used", str(ctx.exception))


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
            self.assertEqual(cloud.resolve_pins(("/bin/tls-pin-get", "host; rm -rf $HOME")), ("c" * 64,))
        self.assertEqual(mock_run.call_args.args, (("/bin/tls-pin-get", "host; rm -rf $HOME"),))
        self.assertNotIn("shell", mock_run.call_args.kwargs)

    def test_command_is_run_once(self):
        with patch("cloud.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, stdout=b"d" * 64 + b"\n", stderr=b"")
            cloud.resolve_pins(("/bin/tls-pin-get", "run-once.example:443"))
            cloud.resolve_pins(("/bin/tls-pin-get", "run-once.example:443"))
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
                cloud.resolve_pins(("/bin/tls-pin-get", "timeout.example:443"))
        self.assertEqual(str(ctx.exception), "Pin command timed out after 10s: /bin/tls-pin-get timeout.example:443")

    def test_command_without_a_full_path_is_not_run(self):
        """Refused when the config is loaded, and here again"""
        for program in ("tls-pin-get", "./tls-pin-get"):
            with self.subTest(program=program), patch("cloud.subprocess.run") as mock_run:
                with self.assertRaises(CloudException) as ctx:
                    cloud.resolve_pins((program, "relative.example:443"))
                mock_run.assert_not_called()
                expected = f"Pin command must start with a full path: {program} relative.example:443"
                self.assertEqual(str(ctx.exception), expected)

    def test_failing_command_means_no_connection(self):
        """And with what went wrong: not as an unknown error"""
        with patch("cloud.open_url") as mock_open_url:
            with self.assertRaises(CloudException) as ctx:
                self.request(self.sh("exit 1"))
        mock_open_url.assert_not_called()
        self.assertEqual(str(ctx.exception), "Pin command failed (exit code 1): /bin/sh -c exit 1")

    def test_resolved_pins_reach_the_ssl_context(self):
        with (
            patch.object(cloud, "make_pinned_ssl_context") as mock_context,
            patch("cloud.open_url") as mock_open_url,
        ):
            mock_open_url.return_value.read.return_value = b'{"ok": true}'
            self.assertEqual(self.request(self.sh(f"echo {'a' * 64}; echo {'b' * 64}")), {"ok": True})
        mock_context.assert_called_once_with(("a" * 64, "b" * 64), cafile="/ca.pem")
        self.assertIs(mock_open_url.call_args.kwargs["context"], mock_context.return_value)

    def test_cafile_can_not_be_forgotten(self):
        with self.assertRaises(TypeError):
            asyncio_run(cloud.make_request(PIN_COMMAND, "GET", "https://x.example/", "", {}))  # ty: ignore[missing-argument]

    def test_pinned_context_accepts_one_or_several_pins(self):
        for pins in ("a" * 64, ("a" * 64, "b" * 64), []):
            with self.subTest(pins=pins):
                context = cloud.make_pinned_ssl_context(pins)
                self.assertTrue(context.check_hostname)


class TestOpenUrl(unittest.TestCase):
    """Requests have a timeout, and a redirect is never followed: the credentials would go along"""

    def setUp(self):
        requests = self.requests = []

        class Handler(BaseHTTPRequestHandler):
            def do_GET(self):
                requests.append((self.path, self.headers.get("X-Auth-Token")))
                if self.path.startswith("/redirect/"):
                    self.send_response(int(self.path.removeprefix("/redirect/")))
                    self.send_header("Location", f"http://127.0.0.1:{self.server.server_port}/elsewhere")
                else:
                    self.send_response(200)
                self.send_header("Content-Length", "0")
                self.end_headers()

            def log_message(self, format, *args):
                pass

        self.server = HTTPServer(("127.0.0.1", 0), Handler)
        Thread(target=self.server.serve_forever, daemon=True).start()
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)

    def open_url(self, path):
        url = f"http://127.0.0.1:{self.server.server_port}{path}"
        request = urllib.request.Request(url, headers={"X-Auth-Token": "secret"})
        return cloud.open_url(request, context=ssl.create_default_context())

    def test_no_redirect_is_followed(self):
        for code in (301, 302, 303, 307, 308):
            self.requests.clear()
            with self.subTest(code=code), self.assertRaises(HTTPError) as ctx:
                self.open_url(f"/redirect/{code}")
            ctx.exception.close()
            self.assertEqual(ctx.exception.code, code)
            self.assertEqual(self.requests, [(f"/redirect/{code}", "secret")])  # and nothing to /elsewhere

    def test_what_is_not_a_redirect_goes_through(self):
        with self.open_url("/fine") as response:
            self.assertEqual(response.status, 200)
        self.assertEqual(self.requests, [("/fine", "secret")])

    def test_redirect_is_reported_as_such(self):
        error = HTTPError("https://cloud.example/", 302, "Found", {}, BytesIO(b""))
        self.addCleanup(error.close)
        with patch("cloud.open_url", side_effect=error), self.assertRaises(CloudException) as ctx:
            asyncio_run(cloud.make_request(PIN_COMMAND, "GET", "https://cloud.example/", "", {}, cafile=None))
        expected = "Cloud answered with a redirect (302): not followed, the credentials would go along"
        self.assertEqual(str(ctx.exception), expected)

    def test_requests_have_a_timeout(self):
        with patch("cloud.urllib.request.build_opener") as mock_build_opener:
            cloud.open_url("request", context=ssl.create_default_context())
        mock_build_opener.return_value.open.assert_called_once_with("request", timeout=cloud.REQUEST_TIMEOUT)


if __name__ == "__main__":
    unittest.main(verbosity=2)
