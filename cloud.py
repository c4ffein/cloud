#!/usr/bin/env python

"""
cloud - KISS cli to interact with cloud providers
MIT License - Copyright (c) 2025 c4ffein
WARNING: I don't recommend using this as-is. This a PoC, and usable by me because I know what I want to do with it.
- You can use it if you feel that you can edit the code yourself and you can live with my future breaking changes.
TODOs and possible improvements: Fill this
- TODO /me/changePassword for ovh
"""

import os
import urllib.request
from asyncio import gather, get_running_loop
from asyncio import run as asyncio_run
from base64 import b64decode
from enum import Enum
from functools import partial
from hashlib import sha1, sha256
from json import dumps, loads
from pathlib import Path
from pprint import pprint as pretty_print  # We may want to redefine a slightly better version
from socket import gaierror
from socket import timeout as socket_timeout
from ssl import (
    CERT_NONE,
    CERT_REQUIRED,
    PROTOCOL_TLS_CLIENT,
    PROTOCOL_TLS_SERVER,
    Purpose,
    SSLCertVerificationError,
    SSLContext,
    SSLSocket,
    _ASN1Object,
    _ssl,
)
from sys import argv, exit
from sys import flags as sys_flags
from time import time as time_time
from urllib.error import HTTPError

CAFILE = None  # Set from config "ssl-cafile", required
LOWER_ALPHANUMERICAL_CHARS = "0123456789abcdefghijklmnopqrstuvwxyz"
ALPHANUMERICAL_CHARS = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"


########################################################################################################################
### Base helpers #######################################################################################################


colors = {"RED": "31", "GREEN": "32", "PURP": "34", "DIM": "90", "WHITE": "39"}
Color = Enum("Color", [(k, f"\033[{v}m") for k, v in colors.items()])


def make_pinned_ssl_context(pinned_sha_256):
    """
    Returns an instance of a subclass of SSLContext that uses a subclass of SSLSocket
    that actually verifies the sha256 of the certificate during the TLS handshake
    Tested with `python-version: [3.8, 3.9, 3.10, 3.11, 3.12, 3.13]`
    Original code can be found at https://github.com/c4ffein/python-snippets
    """

    class PinnedSSLSocket(SSLSocket):
        def check_pinned_cert(self):
            der_cert_bin = self.getpeercert(True)
            if sha256(der_cert_bin).hexdigest() != pinned_sha_256:
                raise SSLCertVerificationError("Incorrect certificate checksum")

        def do_handshake(self, *args, **kwargs):
            r = super().do_handshake(*args, **kwargs)
            self.check_pinned_cert()
            return r

    class PinnedSSLContext(SSLContext):
        sslsocket_class = PinnedSSLSocket

    def create_pinned_default_context(purpose=Purpose.SERVER_AUTH, *, cafile=None, capath=None, cadata=None):
        if not isinstance(purpose, _ASN1Object):
            raise TypeError(purpose)
        if purpose == Purpose.SERVER_AUTH:  # Verify certs and host name in client mode
            context = PinnedSSLContext(PROTOCOL_TLS_CLIENT)
            context.verify_mode, context.check_hostname = CERT_REQUIRED, True
        elif purpose == Purpose.CLIENT_AUTH:
            context = PinnedSSLContext(PROTOCOL_TLS_SERVER)
        else:
            raise ValueError(purpose)
        context.verify_flags |= _ssl.VERIFY_X509_STRICT
        if cafile or capath or cadata:
            context.load_verify_locations(cafile, capath, cadata)
        elif context.verify_mode != CERT_NONE:
            context.load_default_certs(purpose)  # Try loading default system root CA certificates, may fail silently
        if hasattr(context, "keylog_filename"):  # OpenSSL 1.1.1 keylog file
            keylogfile = os.environ.get("SSLKEYLOGFILE")
            if keylogfile and not sys_flags.ignore_environment:
                context.keylog_filename = keylogfile
        return context

    return create_pinned_default_context(cafile=CAFILE)


class CloudException(Exception):
    pass


def confirm(message):
    if input(f"{Color.RED.value}{message}Type YES to confirm:{Color.WHITE.value} ") != "YES":
        raise CloudException("Operation cancelled from user input")


async def make_request(cert_checksum, method, query, body, headers, decode_json=True, decode_utf8=True):
    context = make_pinned_ssl_context(cert_checksum)
    loop = get_running_loop()
    request = urllib.request.Request(query, data=body.encode("utf-8") if body else None, headers=headers, method=method)
    try:
        response = await loop.run_in_executor(None, partial(urllib.request.urlopen, request, context=context))
        data = await loop.run_in_executor(None, response.read)
    except HTTPError as exc:
        additional_infos = ""
        try:
            additional_infos = exc.read()
        except Exception:
            pass
        raise CloudException(
            f"HTTP Error when reaching cloud: {exc.code}"
            + (f"\n{' ' * 8}{additional_infos}" if additional_infos else "")
        ) from exc
    except TimeoutError as exc:
        raise CloudException("Timed out") from exc
    except Exception as exc:
        if isinstance(getattr(exc, "reason", None), socket_timeout):
            raise CloudException("TLS timed out") from exc  # Most probable cause, should check if always the case
        if isinstance(getattr(exc, "reason", None), gaierror):
            raise CloudException("Failed domain name resolution") from exc
        if isinstance(getattr(exc, "reason", None), SSLCertVerificationError):
            raise CloudException("Failed SSL cert validation") from exc
        # Keeping this as-is for now, should not happen if everything is handled correctly, add any necessary ones
        raise CloudException("Unknown error when trying to reach cloud") from exc
    if decode_json:
        try:
            return loads(data)  # handles utf-8 conversion
        except Exception as exc:
            raise CloudException("Unable to parse JSON answer from the response") from exc
    if decode_utf8:
        try:
            return data.decode("utf-8")
        except Exception as exc:
            raise CloudException("Unable to decode utf-8 from the response") from exc
    return data


########################################################################################################################
### OVH ################################################################################################################


class OVHApi:
    def __init__(self, cert_checksum, pdf_cert_checksum, application_key, application_secret, consumer_key):
        self.application_key = application_key
        self.application_secret = application_secret
        self.consumer_key = consumer_key
        # API endpoints
        self.endpoints = {
            "ovh-eu": "https://eu.api.ovh.com/1.0",
            "ovh-us": "https://api.us.ovhcloud.com/1.0",  # unused for now
            "ovh-ca": "https://ca.api.ovh.com/1.0",  # unused for now
        }
        self.base_url = self.endpoints["ovh-eu"]
        self.cert_checksum = cert_checksum
        self.pdf_cert_checksum = pdf_cert_checksum

    # Auth helpers

    def _calculate_signature(self, method, query, body, timestamp):
        """Calculate the API request signature"""
        signature_data = "+".join(
            [self.application_secret, self.consumer_key, method.upper(), query, body or "", str(timestamp)]
        )
        signature = "$1$" + sha1(signature_data.encode("utf-8")).hexdigest()
        return signature

    async def _make_request(self, method, path, data=None, decode_json=True, decode_utf8=True, base_url=None):
        """Make an authenticated request to the OVH API"""
        query = (self.base_url if base_url is None else base_url) + path
        # Prepare body
        body = ""
        headers = {
            "X-Ovh-Application": self.application_key,
            "X-Ovh-Consumer": self.consumer_key,
            "Content-Type": "application/json",
        }
        if data:
            body = dumps(data)
            headers["Content-Length"] = str(len(body))

        # Calculate timestamp and signature
        timestamp = int(time_time())
        headers["X-Ovh-Timestamp"] = str(timestamp)
        headers["X-Ovh-Signature"] = self._calculate_signature(method, query, body, timestamp)
        # Create request
        return await make_request(
            self.cert_checksum if base_url is None else self.pdf_cert_checksum,
            method,
            query,
            body,
            headers,
            decode_json=decode_json,
            decode_utf8=decode_utf8,
        )

    # Invoices

    async def list_invoices(self):
        """List all invoices"""
        invoice_ids = await self._make_request("GET", "/me/bill")
        if any(not all(c in "FR0123456789" for c in invoice_id) for invoice_id in invoice_ids):
            raise CloudException("Invalid invoice id")
        return invoice_ids

    async def get_invoice_details(self, invoice_id):
        """Get details of a specific invoice"""
        if not all(c in "FR0123456789" for c in invoice_id):
            raise CloudException("Invalid invoice id")
        return await self._make_request("GET", f"/me/bill/{invoice_id}")

    async def list_invoices_with_details(self):
        """List all invoices with their details"""
        invoice_ids = await self.list_invoices()
        invoice_ids = invoice_ids[
            -30:
        ]  # TODO better obviously lol, make a cache, only download on cache miss, then unlimit
        try:
            results = await gather(*(self.get_invoice_details(invoice_id) for invoice_id in invoice_ids))
        except Exception as exc:
            raise CloudException(f"Error fetching invoices: {exc}") from exc
        return dict(zip(invoice_ids, results, strict=False))

    async def get_invoice_pdf(self, pdf_url):
        if type(pdf_url) is not str or not pdf_url.startswith("https://www.ovh.com/cgi-bin/order"):
            raise CloudException(f"Invalid pdfUrl {pdf_url}")
        return await self._make_request(
            "GET", pdf_url[33:], decode_json=False, decode_utf8=False, base_url=pdf_url[:33]
        )

    # VPS

    def _validate_vps_id(self, vps_id):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in vps_id):
            raise CloudException("Invalid vps id")

    async def list_vps(self):
        """List all vps"""
        vps_ids = await self._make_request("GET", "/vps")
        for vps_id in vps_ids:
            self._validate_vps_id(vps_id)
        return vps_ids

    async def get_vps_details(self, vps_id):
        """Get details of a specific vps"""
        self._validate_vps_id(vps_id)
        return await self._make_request("GET", f"/vps/{vps_id}")

    async def get_vps_ips(self, vps_id):
        """Get ips of a specific vps"""
        self._validate_vps_id(vps_id)
        return await self._make_request("GET", f"/vps/{vps_id}/ips")

    async def get_vps_service_infos(self, vps_id):
        """Get service_infos of a specific vps"""
        self._validate_vps_id(vps_id)
        return await self._make_request("GET", f"/vps/{vps_id}/serviceInfos")

    async def list_vps_with_details(self):
        """List all vpss with their details"""
        vps_ids = await self.list_vps()

        async def handle(awaitable):
            try:
                return await awaitable
            except Exception:
                return {"error": True}

        tasks = (
            *(handle(self.get_vps_details(vps_id)) for vps_id in vps_ids),
            *(handle(self.get_vps_ips(vps_id)) for vps_id in vps_ids),
            *(handle(self.get_vps_service_infos(vps_id)) for vps_id in vps_ids),
        )
        try:
            results = await gather(*tasks)
        except Exception as exc:
            raise CloudException(f"Error fetching vps: {exc}") from exc
        vps_dict = dict(zip(vps_ids, results[: len(vps_ids)], strict=False))
        for vps_id, ip_data in zip(vps_ids, results[len(vps_ids) : len(vps_ids) * 2], strict=False):
            vps_dict[vps_id]["c4_aggregated_ips"] = ip_data
        for vps_id, service_info_data in zip(vps_ids, results[len(vps_ids) * 2 :], strict=False):
            vps_dict[vps_id]["c4_aggregated_service_infos"] = service_info_data
        return vps_dict

    async def rename_vps(self, vps_id, new_name):
        """Rename a specific vps"""
        self._validate_vps_id(vps_id)
        if type(new_name) is not str:
            raise CloudException("A string is expected as the new vps name")
        return await self._make_request("PUT", f"/vps/{vps_id}", {"displayName": new_name})

    async def list_vps_templates(self, vps_name):
        """WARNING doesn't work for now"""
        self._validate_vps_id(vps_name)
        return await self._make_request("GET", f"/vps/{vps_name}/templates")

    async def reinstall_vps(self, vps_name, ssh_key, template_id=0):
        self._validate_vps_id(vps_name)
        if not all(c in ALPHANUMERICAL_CHARS + ".- @/" for c in ssh_key):
            raise CloudException("Invalid ssh key")
        try:
            template_id = int(template_id)
        except Exception as exc:
            raise CloudException(f"template-id {template_id} must be an int or castable as an int") from exc
        reinstall_body = {
            "templateId": template_id,
            "publicSshKey": ssh_key,
            "doNotSendPassword": True,
        }
        return await self._make_request("POST", f"/vps/{vps_name}/reinstall", reinstall_body)

    # Server

    def _validate_server_id(self, server_id):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in server_id):
            raise CloudException("Invalid server id")

    async def list_server(self):
        """List all server"""
        server_ids = await self._make_request("GET", "/dedicated/server")
        for server_id in server_ids:
            self._validate_server_id(server_id)
        return server_ids

    async def get_server_details(self, server_id):
        """Get details of a specific server"""
        self._validate_server_id(server_id)
        return await self._make_request("GET", f"/dedicated/server/{server_id}")

    async def get_server_ips(self, server_id):
        """Get ips of a specific server"""
        self._validate_server_id(server_id)
        return await self._make_request("GET", f"/dedicated/server/{server_id}/ips")

    async def list_servers_with_details(self):
        """List all servers with their details"""
        server_ids = await self.list_server()
        tasks = (
            *(self.get_server_details(server_id) for server_id in server_ids),
            *(self.get_server_ips(server_id) for server_id in server_ids),
        )
        try:
            results = await gather(*tasks)
        except Exception as exc:
            raise CloudException(f"Error fetching server: {exc}") from exc
        server_dict = dict(zip(server_ids, results[: len(server_ids)], strict=False))
        for server_id, ip_data in zip(server_ids, results[len(server_ids) :], strict=False):
            server_dict[server_id]["c4_aggregated_ips"] = ip_data
        return server_dict

    async def reinstall_server(self, server_name, ssh_key, operating_system="debian12_64"):
        self._validate_server_id(server_name)
        if not all(c in ALPHANUMERICAL_CHARS + ".- @/" for c in ssh_key):
            raise CloudException("Invalid ssh key")
        reinstall_body = {
            "operatingSystem": operating_system,
            "customizations": {"sshKey": ssh_key},
        }
        return await self._make_request("POST", f"/dedicated/server/{server_name}/reinstall", reinstall_body)

    async def monitor_server_reinstallation(self, server_name):
        self._validate_server_id(server_name)
        return await self._make_request("GET", f"/dedicated/server/{server_name}/install/status")

    # SSH keys

    async def list_ssh_keys(self):
        """List all SSH keys in your OVH account"""
        ssh_key_names = await self._make_request("GET", "/me/sshKey")
        if any(not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in key_name) for key_name in ssh_key_names):
            raise CloudException("Invalid ssh key name")
        results = await gather(*(self._make_request("GET", f"/me/sshKey/{key_name}") for key_name in ssh_key_names))
        return dict(zip(ssh_key_names, results, strict=False))

    async def add_ssh_key(self, name, key):
        """Add an ssh key to your OVH account"""
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in name):
            raise CloudException("Invalid ssh key name")
        if not all(c in ALPHANUMERICAL_CHARS + ".-@ " for c in key):
            raise CloudException("Invalid ssh key")
        return await self._make_request("POST", "/me/sshKey", {"keyName": name, "key": key})

    # Domains

    def _validate_domain(self, domain):
        if any(c not in ALPHANUMERICAL_CHARS + "." for c in domain):
            raise CloudException("Invalid domain")

    def _validate_record_id(self, record_id):
        if any(c not in LOWER_ALPHANUMERICAL_CHARS + "-." for c in str(record_id)):
            raise CloudException("Invalid record id")

    async def list_domain(self):
        """List all domains"""
        response = await self._make_request("GET", "/domain")
        if type(response) is not list or any(type(item) is not str for item in response):
            raise CloudException("Invalid domain list")
        return response

    async def info_domain(self, domain):
        """All info for a domain"""
        self._validate_domain(domain)
        tasks = (
            self._make_request("GET", f"/domain/{domain}"),  # Basic domain information
            self._make_request("GET", f"/domain/{domain}/serviceInfos"),  # Service details (expiration, renewal status)
            self._make_request("GET", f"/domain/zone/{domain}/record"),  # DNS records
            self._make_request("GET", f"/domain/{domain}/nameServer"),  # Nameserver configuration
            self._make_request("GET", f"/domain/{domain}/option"),  # Domain options (DNSSEC, etc.)
            self._make_request("GET", f"/domain/{domain}/configurations/optin"),
            self._make_request("GET", f"/domain/{domain}/glueRecord"),  # Glue records if any
        )
        tasks_keys = (
            "basic",
            "service_infos",
            "record_ids",
            "name_server_ids",
            "option",
            "configurations_optin",
            "glue_record",
        )
        try:
            results = await gather(*tasks)
        except Exception as exc:
            raise CloudException(f"Error fetching domain data: {exc}") from exc
        infos = dict(zip(tasks_keys, results, strict=False))
        if any(type(id_) is not int for id_ in infos["record_ids"]):
            raise CloudException("Invalid record id")
        if any(type(id_) is not int for id_ in infos["name_server_ids"]):
            raise CloudException("Invalid name server id")
        try:
            additional_results = await gather(
                *(self._make_request("GET", f"/domain/zone/{domain}/record/{id}") for id in infos["record_ids"]),
                *(self._make_request("GET", f"/domain/{domain}/nameServer/{id}") for id in infos["name_server_ids"]),
            )
        except Exception as exc:
            raise CloudException(f"Error fetching domain data: {exc}") from exc
        infos["records"] = dict(
            zip(infos["record_ids"], additional_results[0 : len(infos["record_ids"])], strict=False)
        )
        infos["name_servers"] = dict(
            zip(infos["name_server_ids"], additional_results[len(infos["record_ids"]) :], strict=False)
        )
        return infos

    async def domain_refresh(self, domain):
        """WARNING This needs to be called after record changes"""
        self._validate_domain(domain)
        return await self._make_request("POST", f"/domain/zone/{domain}/refresh")

    async def domain_get_record(self, domain, record_id):
        self._validate_domain(domain)
        self._validate_record_id(record_id)
        return await self._make_request("GET", f"/domain/zone/{domain}/record/{record_id}")

    async def domain_add_record(self, domain, field_type, sub_domain, target, ttl):
        self._validate_domain(domain)
        record = {"fieldType": str(field_type), "subDomain": str(sub_domain), "target": str(target), "ttl": int(ttl)}
        return await self._make_request("POST", f"/domain/zone/{domain}/record", record)

    async def domain_update_record(self, domain, record_id, field_type=None, sub_domain=None, target=None, ttl=None):
        """Uses POST to /record (not PUT to /record/{record_id}) — worked when last tested, OVH API may not support PUT"""
        self._validate_domain(domain)
        self._validate_record_id(record_id)
        record = {"fieldType": field_type, "subDomain": sub_domain, "target": target, "ttl": ttl}
        record = {k: str(v) if k != "ttl" else int(v) for k, v in record.items() if v is not None}
        return await self._make_request("POST", f"/domain/zone/{domain}/record", record)

    async def domain_delete_record(self, domain, record_id):
        self._validate_domain(domain)
        self._validate_record_id(record_id)
        return await self._make_request("DELETE", f"/domain/zone/{domain}/record/{record_id}")

    # Cart

    def _validate_cart_id(self, cart_id):
        if not all(c in "0123456789abcdef-" for c in cart_id):
            raise CloudException("Invalid cart id")

    async def create_cart(self, description):
        return await self._make_request("POST", "/order/cart", {"ovhSubsidiary": "FR", "description": description})

    async def get_cart(self, cart_id):  # includes the list of items
        self._validate_cart_id(cart_id)
        return await self._make_request("GET", f"/order/cart/{cart_id}")

    async def get_cart_checkout_infos(self, cart_id):  # includes checkout infos actually
        self._validate_cart_id(cart_id)
        return await self._make_request("GET", f"/order/cart/{cart_id}/checkout")

    async def checkout_cart(self, cart_id):
        self._validate_cart_id(cart_id)
        return await self._make_request("POST", f"/order/cart/{cart_id}/checkout")

    async def assign_cart(self, cart_id):
        self._validate_cart_id(cart_id)
        return await self._make_request("POST", f"/order/cart/{cart_id}/assign")

    async def cancel_cart(self, cart_id):
        self._validate_cart_id(cart_id)
        return await self._make_request("DELETE", f"/order/cart/{cart_id}")

    async def add_domain_to_cart(self, domain_name, cart_id):
        self._validate_cart_id(cart_id)
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in domain_name):
            raise CloudException("Invalid domain name")
        return await self._make_request(
            "POST",
            f"/order/cart/{cart_id}/domain",
            {
                "domain": domain_name,
                "duration": "P1Y",  # 1 year
                # "duration": "P2Y",  # 2 year  # should parameterize
                "offerId": "domain_offer_id",
            },
        )

    # Emails

    def _validate_email_domain_name(self, domain_name):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in domain_name):
            raise CloudException("Invalid email domain name")

    def _validate_email_account_name(self, account_name):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-_" for c in account_name):
            raise CloudException("Invalid email account name")

    async def list_all_email_domains(self):
        return await self._make_request("GET", "/email/domain")

    async def get_details_for_a_specific_domain(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}")

    async def list_email_accounts_for_a_domain(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/account")

    async def get_account_details(self, domain_name, account_name):
        """account_name of the form user"""
        self._validate_email_domain_name(domain_name)
        self._validate_email_account_name(account_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/account/{account_name}")

    async def create_a_new_email_account(self, domain_name, account_name, password, description, size):
        """size is in bytes"""
        self._validate_email_domain_name(domain_name)
        self._validate_email_account_name(account_name)
        new_account_data = {"accountName": account_name, "password": password, "description": description, "size": size}
        return await self._make_request("POST", f"/email/domain/{domain_name}/account", new_account_data)

    async def update_account_quota(self, domain_name, account_name, size):
        self._validate_email_domain_name(domain_name)
        self._validate_email_account_name(account_name)
        update_data = {"size": size}  # in bytes
        return await self._make_request("PUT", f"/email/domain/{domain_name}/account/{account_name}", update_data)

    async def delete_an_email_account(self, domain_name, account_name):
        self._validate_email_domain_name(domain_name)
        self._validate_email_account_name(account_name)
        return await self._make_request("DELETE", f"/email/domain/{domain_name}/account/{account_name}")

    async def list_email_redirections(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/redirection")

    async def create_a_redirection(self, domain_name, email_from, email_to, local_copy):
        self._validate_email_domain_name(domain_name)
        redirection_data = {"from": email_from, "to": email_to, "localCopy": local_copy}
        return await self._make_request("POST", f"/email/domain/{domain_name}/redirection", redirection_data)

    async def check_domain_quota_usage(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/quota")

    async def get_service_information(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/serviceInfos")

    async def check_if_you_can_order_additional_resources(self, domain_name):
        self._validate_email_domain_name(domain_name)
        return await self._make_request("GET", f"/email/domain/{domain_name}/availableOffer")

    # Telephony Voicemail

    def _validate_billing_account(self, billing_account):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in billing_account):
            raise CloudException("Invalid billing account")

    def _validate_service_name(self, service_name):
        if not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in service_name):
            raise CloudException("Invalid service name")

    async def list_telephony_services(self):
        """List all telephony services (billing accounts)"""
        billing_accounts = await self._make_request("GET", "/telephony")
        if any(not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in account) for account in billing_accounts):
            raise CloudException("Invalid billing account")
        return billing_accounts

    async def list_voicemail_services(self, billing_account):
        """List all voicemail services for a billing account"""
        self._validate_billing_account(billing_account)
        services = await self._make_request("GET", f"/telephony/{billing_account}/voicemail")
        if any(not all(c in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in service) for service in services):
            raise CloudException("Invalid voicemail service")
        return services

    async def list_voicemail_messages(self, billing_account, service_name):
        """List all voicemail messages (directories)"""
        self._validate_billing_account(billing_account)
        self._validate_service_name(service_name)
        messages = await self._make_request("GET", f"/telephony/{billing_account}/voicemail/{service_name}/directories")
        return messages

    async def get_voicemail_message_details(self, billing_account, service_name, message_id):
        """Get details of a specific voicemail message"""
        self._validate_billing_account(billing_account)
        self._validate_service_name(service_name)
        try:
            message_id = int(message_id)
        except ValueError:
            raise CloudException("Message ID must be an integer") from None
        return await self._make_request(
            "GET", f"/telephony/{billing_account}/voicemail/{service_name}/directories/{message_id}"
        )

    async def download_voicemail_message(self, billing_account, service_name, message_id, audio_format="wav"):
        """Download a voicemail message"""
        self._validate_billing_account(billing_account)
        self._validate_service_name(service_name)
        try:
            message_id = int(message_id)
        except ValueError:
            raise CloudException("Message ID must be an integer") from None
        if audio_format not in ["wav", "mp3"]:
            raise CloudException("Audio format must be 'wav' or 'mp3'")
        return await self._make_request(
            "GET",
            f"/telephony/{billing_account}/voicemail/{service_name}/directories/{message_id}/download",
            data={"format": audio_format},
            decode_json=False,
            decode_utf8=False,
        )

    async def download_voicemail_greeting(self, billing_account, service_name, greeting_id, audio_format="wav"):
        """Download a voicemail greeting"""
        self._validate_billing_account(billing_account)
        self._validate_service_name(service_name)
        try:
            greeting_id = int(greeting_id)
        except ValueError:
            raise CloudException("Greeting ID must be an integer") from None
        if audio_format not in ["wav", "mp3"]:
            raise CloudException("Audio format must be 'wav' or 'mp3'")
        return await self._make_request(
            "GET",
            f"/telephony/{billing_account}/voicemail/{service_name}/greetings/{greeting_id}/download",
            data={"format": audio_format},
            decode_json=False,
            decode_utf8=False,
        )

    async def get_voicemail_settings(self, billing_account, service_name):
        """Get voicemail settings"""
        self._validate_billing_account(billing_account)
        self._validate_service_name(service_name)
        return await self._make_request("GET", f"/telephony/{billing_account}/voicemail/{service_name}/settings")

    # Orders

    def _validate_order_id(self, order_id):
        if not all(c in "0123456789" for c in str(order_id)):
            raise CloudException("Invalid order id")

    async def list_orders(self):
        orders = await self._make_request("GET", "/me/order")
        for order in orders:
            self._validate_order_id(order)
        results = await gather(*(self._make_request("GET", f"/me/order/{order}") for order in orders))
        return dict(zip(orders, results, strict=False))

    async def pay_order(self, order_id, payment_method_id):
        """WARNING only handles credit cards for now - AND NEVER WORKED FOR DOMAINS!"""
        self._validate_order_id(order_id)
        if not all(c in "0123456789" for c in str(payment_method_id)):
            raise CloudException("Invalid payment method id")
        return await self._make_request(
            "POST",
            f"/me/order/{order_id}/payWithRegisteredPaymentMean",
            {"paymentMean": "CREDIT_CARD", "paymentMeanId": payment_method_id},
        )

    # Payment methods

    async def get_payment_methods(self):
        methods = await self._make_request("GET", "/me/payment/method")
        if type(methods) is not list or any(type(v) is not int for v in methods):
            raise CloudException(f"Unexpected return value for /me/payment/method: {methods}")
        results = await gather(*(self._make_request("GET", f"/me/payment/method/{k}") for k in methods))
        return dict(zip(methods, results, strict=False))


########################################################################################################################
### Scaleway ###########################################################################################################


class ScalewayApi:
    def __init__(self, cert_checksum, secret_key, organization_id):
        self.cert_checksum = cert_checksum
        self.secret_key = secret_key
        self.organization_id = organization_id
        self.base_url = "https://api.scaleway.com"

    # Auth helpers

    async def _make_request(self, method, path, data=None, decode_json=True, decode_utf8=True):
        """Make an authenticated request to the Scaleway API"""
        query = self.base_url + path
        # Prepare body
        body = ""
        headers = {"X-Auth-Token": self.secret_key, "Content-Type": "application/json"}
        if data:
            body = dumps(data)
            headers["Content-Length"] = str(len(body))
        # Create request
        return await make_request(
            self.cert_checksum, method, query, body, headers, decode_json=decode_json, decode_utf8=decode_utf8
        )

    # Invoices

    async def list_invoices(self):
        """List all invoices"""
        invoices_data = await self._make_request("GET", "/billing/v2beta1/invoices")
        invoices_data_list = invoices_data["invoices"]
        if any(not all(c in "0123456789abcdef-" for c in invoice["id"]) for invoice in invoices_data_list):
            raise CloudException("Invalid invoice id")
        if any(not all(c in "0123456789TZ-:." for c in invoice["issued_date"]) for invoice in invoices_data_list):
            raise CloudException("Invalid issued date")
        return invoices_data_list

    async def get_invoice_pdf(self, invoice_id):
        if type(invoice_id) is not str or any(c not in "0123456789abcdef-" for c in invoice_id):
            raise CloudException(f"Invalid invoice id {invoice_id}")
        r = await self._make_request("GET", f"/billing/v2beta1/invoices/{invoice_id}/download")
        if any(c not in LOWER_ALPHANUMERICAL_CHARS + ".-" for c in r["name"]):
            raise CloudException(f"Invalid invoice name {r['name']}")
        try:
            bytes_content = b64decode(r["content"])
        except Exception:
            raise CloudException("Unable to b64decode invoice pdf content") from None
        return r["name"], bytes_content

    # Servers

    async def list_servers(self):
        print(f"{Color.RED.value}WARNING: ONLY CHECKING A SINGLE ZONE FOR NOW...{Color.WHITE.value}")
        return await self._make_request("GET", "/instance/v1/zones/fr-par-1/servers")

    async def remove_server(self, server_id):
        server_id = server_id.lower()
        if not all(c in "0123456789abcdef-" for c in server_id) or len(server_id) != 36:
            raise CloudException("Invalid server id")
        print(f"{Color.RED.value}WARNING: ONLY CHECKING A SINGLE ZONE FOR NOW...{Color.WHITE.value}")
        return await self._make_request("DELETE", f"/instance/v1/zones/fr-par-1/servers/{server_id}")

    async def terminate_server(self, server_id):
        server_id = server_id.lower()
        if not all(c in "0123456789abcdef-" for c in server_id) or len(server_id) != 36:
            raise CloudException("Invalid server id")
        print(f"{Color.RED.value}WARNING: ONLY CHECKING A SINGLE ZONE FOR NOW...{Color.WHITE.value}")
        return await self._make_request(
            "POST", f"/instance/v1/zones/fr-par-1/servers/{server_id}/action", {"action": "terminate"}
        )

    # Domains

    async def list_domains(self):
        return await self._make_request("GET", "/domain/v2beta1/dns-zones")

    async def get_domain(self, project_id):
        if type(project_id) is not str or any(c not in "0123456789abcdef-" for c in project_id):
            raise CloudException(f"Invalid project-id {project_id}")
        return await self._make_request("GET", f"/domain/v2beta1/dns-zones/{project_id}")


########################################################################################################################
### Config #############################################################################################################


class CloudConfig:
    name = None
    required = []
    optional = ["invoice-path"]

    def __init__(self, config_dict):
        missing_keys = set(self.required) - set(config_dict.keys())
        unknown_keys = set(config_dict.keys()) - set(self.required) - set(self.optional)
        if missing_keys:
            raise CloudException(f"Missing keys for {self.name} options: {missing_keys}")
        if unknown_keys:
            raise CloudException(f"Unknown keys for {self.name} options: {unknown_keys}")
        for k, v in config_dict.items():
            setattr(self, k.replace("-", "_"), v)
        for k in self.optional:
            if not hasattr(self, k.replace("-", "_")):
                setattr(self, k.replace("-", "_"), None)
        if type(self.certificate) is not str or len(self.certificate) != 64:
            raise CloudException(f"Unexpected certificate format for {self.name} certificate {self.certificate}")
        if self.invoice_path is not None:
            if "{year}" not in self.invoice_path or "{invoice_id}" not in self.invoice_path:
                raise CloudException(
                    f"{self.name} 'invoice-path' must contain {{year}} and {{invoice_id}} placeholders"
                )


class OVHConfig(CloudConfig):
    name = "OVH"
    required = ["certificate", "application-key", "application-secret", "consumer-key", "pdf-certificate"]


class ScalewayConfig(CloudConfig):
    name = "Scaleway"
    required = ["certificate", "secret-key", "organization-id"]


def load_config():
    global CAFILE
    try:
        with (Path.home() / ".config" / "cloud" / "config.json").open() as f:
            config_content = f.read()
    except Exception:
        return None
    try:
        config_dict = loads(config_content)
    except Exception:
        raise CloudException("Unable to parse config file as json") from None
    if "ssl-cafile" not in config_dict or type(config_dict["ssl-cafile"]) is not str:
        raise CloudException("Missing or invalid 'ssl-cafile' in config")
    CAFILE = config_dict["ssl-cafile"]
    return OVHConfig(config_dict.get("ovh", {})), ScalewayConfig(config_dict.get("scaleway", {}))


########################################################################################################################
### CLI ################################################################################################################


def usage(wrong_config=False):
    output_lines = [
        "cloud - KISS clouds bridge to your terminal",
        "───────────────────────────────────────────",
        """~/.config/cloud/config.json => {"ssl-cafile": "/path/to/cacert.pem",""",
        """                                "ovh": {...}, "scaleway": {...}}""",
        "───────────────────────────────────────────",
        "You can set /* for any verb when generating your OVH api key",
        "───────────────────────────────────────────",
        """""",
        f"""{Color.PURP.value}You must select a cloud first""",
        f"""{Color.DIM.value} - {Color.WHITE.value}cloud ovh""",
        f"""{Color.DIM.value} - {Color.WHITE.value}cloud scaleway""",
    ]
    print("\n" + "\n".join(output_lines) + "\n")
    return -1


def consume_parameters(args, mandatories=None, optionals=None):
    mandatories, optionals = [] if mandatories is None else mandatories, [] if optionals is None else optionals
    if len(set(mandatories) | set(optionals)) != len(set(mandatories)) + len(set(optionals)):
        raise Exception("mandatories and optionals need to be separate collections")
    missing_mandatories = [m for m in mandatories if not any(a.startswith(f"{m}=") for a in args)]
    if missing_mandatories:
        raise CloudException(f"Missing mandatory parameters: {missing_mandatories}")
    return (
        [a for a in args if not any(a.startswith(f"{p}=") for p in (*mandatories, *optionals))],
        {a[: len(n)]: a[len(n) + 1 :] for a in args for n in (*mandatories, *optionals) if a.startswith(f"{n}=")},
    )


async def ovh_invoice(ovh_api, ovh_config):
    if not ovh_config.invoice_path:
        raise CloudException("Missing 'invoice-path' in OVH config (use {year} for year from invoice date)")
    invoices = await ovh_api.list_invoices_with_details()
    downloaded_count = 0
    for invoice_id, invoice in invoices.items():
        if not isinstance(invoice.get("date"), str):
            raise CloudException("Can't find date as str for invoice")
        if not all(c in "0123456789-" for c in invoice["date"][:10]):
            raise CloudException("Invalid date for invoice")
        if not isinstance(invoice.get("priceWithTax"), dict):
            raise CloudException("Invalid priceWithTax infos for invoice")
        value = invoice["priceWithTax"].get("value")
        if type(value) is not int and type(value) is not float:
            raise CloudException(f"Invalid priceWithTax value type {type(value)} for invoice")
        value = f"{value:.2f}"
        if type(invoice["date"]) is not str:
            raise CloudException("Invalid type for date of invoice")
        printable_date = invoice["date"][:10]
        if not all(c in "0123456789-" for c in printable_date):
            raise CloudException(f"Unexpected date format for invoice {invoice_id}: {invoice['date']}")
        invoice_year = invoice["date"][:4]
        if len(invoice_year) != 4 or not all(c in "0123456789" for c in invoice_year):
            raise CloudException(f"Unexpected date format for invoice {invoice_id}: {invoice['date']}")
        pdf_path = Path(
            ovh_config.invoice_path.format(
                year=invoice_year, invoice_id=invoice_id, value=value, printable_date=printable_date
            )
        )
        pdf_path_tmp = Path(f"{pdf_path}.tmp")
        if not pdf_path.exists():
            print(f"Downloading {invoice_id}")
            print(invoice)
            pdf_url = invoice.get("pdfUrl")
            downloaded_pdf_content = await ovh_api.get_invoice_pdf(pdf_url)
            print(f"=> Writing {pdf_path_tmp}")
            if not pdf_path_tmp.parent.exists():
                raise CloudException(f"Directory does not exist: {pdf_path_tmp.parent}")
            with pdf_path_tmp.open("wb") as f:
                f.write(downloaded_pdf_content)
            with pdf_path_tmp.open("rb") as f:
                verif_pdf_content = f.read()
            if not verif_pdf_content.startswith(b"%PDF-1.") or verif_pdf_content != downloaded_pdf_content:  # paranoid
                raise CloudException(f"Error on invoice save: check {pdf_path_tmp}")
            pdf_path_tmp.rename(pdf_path)
            print(f"=> Validated and moved to {pdf_path}")
            downloaded_count += 1
    print(f"Downloaded {downloaded_count}/{len(invoices)} invoices")


async def ovh_vps_list(ovh_api):
    vps_dict = await ovh_api.list_vps_with_details()
    for vps_id, vps_data in vps_dict.items():
        service_infos = vps_data.get("c4_aggregated_service_infos", {})
        renew_infos = service_infos.get("renew", {})
        will_renew = (renew_infos.get("automatic") and not renew_infos.get("deleteAtExpiration")) or renew_infos.get(
            "forced"
        )
        inconsistent_renew_infos = (
            not renew_infos  # indirectly checks that service_infos is not {}
            or renew_infos.get("automatic") is None
            or renew_infos.get("deleteAtExpiration") is None
            or renew_infos.get("forced") is None
            or (  # edge case, we tried to configure expiration, but we are still bound...
                renew_infos.get("forced")  # in theory, will be renewed anyway, but better show warning
                and (not renew_infos.get("automatic") or not renew_infos.get("deleteAtExpiration"))
            )
        )
        print(
            f"{Color.PURP.value}{vps_id} {Color.DIM.value}{'─' * (26 - len(str(vps_id)))} "
            f"{Color.GREEN.value if will_renew else Color.RED.value}{str(vps_data.get('displayName'))} "
            f"{Color.DIM.value}{'─' * (72 - len(str(vps_data.get('displayName'))))} ["
            f"{Color.GREEN.value if will_renew else Color.RED.value}"
            f"{'RENEW' if will_renew else 'FINAL'}={service_infos.get('expiration')}{Color.DIM.value}]"
            f"{Color.RED.value}{'  !! INCONSISTENT RENEW INFOS !!  ' if inconsistent_renew_infos else ''}"
        )
        print(
            f"{Color.WHITE.value}{vps_data.get('model', {}).get('memory', 'UNKNOWN')}"
            f" / {vps_data.get('memoryLimit', 'UNKNOWN')}"  # TODO check this
        )
        print(vps_data.get("c4_aggregated_ips", ""))
        # pretty_print(vps_data)
        print()


async def ovh_vps_reinstall(ovh_api, vps_id, ssh_key):
    print(
        "The reinstallation process will wipe all data on the vps and install the specified OS template.\n"
        "The vps will be unavailable during this process, "
        "which typically takes 10-30 minutes depending on the template and vps specifications."
    )
    confirm(f"Will wipe vps {vps_id}. ")
    response = await ovh_api.reinstall_vps(vps_id, ssh_key)
    if type(response) is not dict:
        print(f"{Color.RED.value}WARNING: UNEXPECTED RESPONSE TYPE{Color.WHITE.value}")
        print(response)
        return
    print(f"{Color.DIM.value}Infos:{Color.WHITE.value}")
    for k, v in response.items():
        print(f"  {Color.PURP.value}{str(k).ljust(10)}{Color.DIM.value}={Color.WHITE.value} {str(v)}")


async def ovh_vps(ovh_api, args):
    if args == ["list"]:
        return await ovh_vps_list(ovh_api)
    if len(args) == 3 and args[0] == "rename":
        confirm(f"Are you sure you want to rename {args[1]} to {args[2]}? ")
        response = await ovh_api.rename_vps(args[1], args[2])
        pretty_print(response)
        return
    if len(args) == 2 and args[0] == "list-templates":
        response = await ovh_api.list_vps_templates(args[1])
        pretty_print(response)
        return
    if len(args) == 3 and args[0] == "reinstall":
        return await ovh_vps_reinstall(ovh_api, args[1], args[2])
    print(
        f"{Color.PURP.value}Help\n"
        f" {Color.DIM.value}- {Color.WHITE.value}cloud ovh vps list\n"
        f" {Color.DIM.value}- {Color.WHITE.value}cloud ovh vps rename vps-id new-name\n"
        f" {Color.DIM.value}- {Color.WHITE.value}cloud ovh vps list-templates vps-id\n"
        f" {Color.DIM.value}- {Color.WHITE.value}cloud ovh vps reinstall vps-id ssh-key"
    )


async def ovh_servers(ovh_api):
    server_dict = await ovh_api.list_servers_with_details()
    for server_id, server_data in server_dict.items():
        print(f"{server_id}: {server_data.get('displayName')}")
        print(f"{server_data.get('commercialRange', 'UNKNOWN')}")
        print(server_data.get("c4_aggregated_ips", ""))
        print()


async def ovh_servers_reinstall(ovh_api, server_name, ssh_key):
    print(
        "The reinstallation process will wipe all data on the server and install the specified OS template.\n"
        "The server will be unavailable during this process, "
        "which typically takes 10-30 minutes depending on the template and server specifications."
    )
    confirm(f"Will wipe server {server_name}. ")
    response = await ovh_api.reinstall_server(server_name, ssh_key)
    if type(response) is not dict:
        print(f"{Color.RED.value}WARNING: UNEXPECTED RESPONSE TYPE{Color.WHITE.value}")
        print(response)
        return
    print(f"{Color.DIM.value}Infos:{Color.WHITE.value}")
    for k, v in response.items():
        print(f"  {Color.PURP.value}{str(k).ljust(10)}{Color.DIM.value}={Color.WHITE.value} {str(v)}")


async def ovh_servers_monitor_reinstall(ovh_api, server_name):
    response = await ovh_api.monitor_server_reinstallation(server_name)
    if type(response) is not dict or type(response.get("progress")) is not list:
        print(f"{Color.RED.value}WARNING: UNEXPECTED RESPONSE TYPE{Color.WHITE.value}")
        print(response)
        return
    print(f"{Color.PURP.value}elapsedTime: {Color.WHITE.value}{response.get('elapsedTime')}")
    print(f"{Color.PURP.value}progress:{Color.WHITE.value}")
    for progress_element in response["progress"]:
        if type(progress_element) is not dict:
            print(f"  {Color.RED.value}{progress_element}{Color.WHITE.value}")
            continue
        unhandled_part = {k: v for k, v in progress_element.items() if k not in ["error", "status", "comment"]}
        status = progress_element.get("status")
        status = {
            "done": f"{Color.GREEN.value}{status}{Color.WHITE.value}",
            "doing": f"{Color.PURP.value}{status}{Color.WHITE.value}",
            "todo": f"{Color.DIM.value}{status}{Color.WHITE.value}",
        }.get(status, f"{Color.RED.value}{status}{Color.WHITE.value}").ljust(16)
        error = f"{Color.RED.value}{progress_element.get('error', '')}{Color.WHITE.value}"
        print(f"  {status} {error} {progress_element.get('comment', '')} {unhandled_part or ''}")
    for key, data in {k: v for k, v in response.items() if k not in ["elapsedTime", "progress"]}.items():
        print(f"{Color.RED.value}WARNING: UNHANDLED KEY {key} ={Color.WHITE.value} {data}")


async def ovh_ssh_keys(ovh_api, args):
    if args == ["list"]:
        ssh_keys_dict = await ovh_api.list_ssh_keys()
        for key_name, key_data in ssh_keys_dict.items():
            print(f"{key_name}: {key_data}")
        return
    if len(args) == 3 and args[0] == "add":
        pretty_print(await ovh_api.add_ssh_key(args[1], args[2]))
        return
    print("cloud ovh ssh-key list\ncloud ovh ssh-key add name key")


async def ovh_domain(ovh_api, args):
    async def refresh_zone(domain):
        print(f"{Color.PURP.value} ! Now refreshing !")
        response_to_refresh = await ovh_api.domain_refresh(domain)
        if response_to_refresh is not None:
            raise CloudException("Failed refresh")
        print(f"{Color.GREEN.value} ! Refreshed      !")

    if not args:
        response = await ovh_api.list_domain()
        print(*(f"{Color.DIM.value} - {Color.WHITE.value}{e}" for e in response), sep="\n")
        return
    if len(args) == 2 and args[0] == "info":
        response = await ovh_api.info_domain(args[1])
        handled_basics = ["domain", "contactAdmin", "contactBilling", "contactOwner", "contactTech"]
        basic_dict = response["basic"]
        print(f"{Color.GREEN.value}{basic_dict['domain']}{Color.DIM.value}")
        contact_keys = ["contactAdmin", "contactBilling", "contactOwner", "contactTech"]
        print({k: v for k, v in basic_dict.items() if k in contact_keys})
        pretty_print({k: v for k, v in basic_dict.items() if k not in handled_basics})
        print(f"{Color.GREEN.value}UNHANDLED INFOS{Color.DIM.value}")
        unhandled_domain_keys = ["basic", "record_ids", "name_server_ids", "records"]
        pretty_print({k: v for k, v in response.items() if k not in unhandled_domain_keys})
        print(f"{Color.GREEN.value}RECORDS{Color.DIM.value}")
        record_handled_keys = ["fieldType", "id", "subDomain", "zone", "target", "ttl"]
        for record_id, record in response["records"].items():
            clean_record = {k: v for k, v in record.items() if k not in record_handled_keys}
            print(
                f"{Color.DIM.value}{record_id} {Color.GREEN.value}{record['fieldType'].ljust(5)} "
                f"{Color.DIM.value}[{Color.GREEN.value}{record['subDomain'].rjust(5)}{Color.DIM.value}]"
                f"[{Color.PURP.value}{record['zone']}{Color.DIM.value}]"
                f"[target={Color.GREEN.value}{record['target']}{Color.DIM.value}]"
                f"[ttl={Color.GREEN.value}{record['ttl']}{Color.DIM.value}]"
                f"{Color.WHITE.value}{clean_record or ''}"
            )
        return
    if len(args) == 4 and args[0] == "zone" and args[2] == "get":
        response = await ovh_api.domain_get_record(args[1], args[3])
        pretty_print(response)
        return
    if len(args) > 2 and args[0] == "zone" and args[2] == "add":
        nargs, optionals = consume_parameters(args[3:], mandatories=["field-type", "sub-domain", "target", "ttl"])
        if len(nargs) != 0:
            raise CloudException(f"Found unknown parameter: {nargs}")
        optionals = {k.replace("-", "_"): v for k, v in optionals.items()}
        response_to_add = await ovh_api.domain_add_record(args[1], **optionals)
        pretty_print({"added zone": response_to_add})
        await refresh_zone(args[1])
        return
    if len(args) > 2 and args[0] == "zone" and args[2] == "edit":
        nargs, optionals = consume_parameters(
            args[3:], mandatories=["field-type", "target"], optionals=["sub-domain", "ttl"]
        )
        if len(nargs) == 0:
            raise CloudException("Specify the zone to edit")
        if len(nargs) > 1:
            raise CloudException(f"Found unknown parameter: {nargs}")
        print(f"  {Color.RED.value}!! WARNING this created a new zone, delete previous manually !!{Color.WHITE.value}")
        optionals = {k.replace("-", "_"): v for k, v in optionals.items()}
        response_to_add = await ovh_api.domain_update_record(args[1], nargs[0], **optionals)
        pretty_print({"edited zone": response_to_add})
        await refresh_zone(args[1])
        return
    if len(args) == 4 and args[0] == "zone" and args[2] == "delete":
        RED, WHITE = Color.RED.value, Color.WHITE.value
        confirm(f"Delete zone {WHITE}{args[3]}{RED} from domain {WHITE}{args[1]}{RED}? ")
        response = await ovh_api.domain_delete_record(args[1], args[3])
        pretty_print(response)
        await refresh_zone(args[1])
        return
    baseline = f"{Color.DIM.value} - {Color.WHITE.value}{Color.PURP.value}cloud ovh domain{Color.WHITE.value} "
    print(
        f"{Color.DIM.value}Help\n"
        f"{baseline}\n"
        f"{baseline}info my.domain.ovh\n"
        f"{baseline}zone my.domain.ovh get zone-id\n"
        f"{baseline}zone my.domain.ovh delete zone-id\n"
        f"{baseline}zone my.domain.ovh add field-type=... sub-domain=... target=... ttl=...\n"
        f"{baseline}zone my.domain.ovh edit [field-type=...] [sub-domain=...] [target=...] [ttl=...]\n"
    )


async def ovh_email(ovh_api, args):
    if len(args) == 1 and args[0] == "list":
        pretty_print(await ovh_api.list_all_email_domains())
        return
    if len(args) == 2 and args[0] == "list":
        pretty_print(await ovh_api.list_email_accounts_for_a_domain(args[1]))
        return
    if len(args) == 2 and args[0] == "info":
        pretty_print(await ovh_api.get_details_for_a_specific_domain(args[1]))
        return
    if len(args) == 3 and args[0] == "info":
        pretty_print(await ovh_api.get_account_details(args[1], args[2]))
        return
    if len(args) == 6 and args[0] == "create-account":
        pretty_print(await ovh_api.create_a_new_email_account(*args[1:]))
        return
    if len(args) == 4 and args[0] == "update-account-quota":
        pretty_print(await ovh_api.update_account_quota(*args[1:]))
        return
    if len(args) == 3 and args[0] == "delete-account":
        pretty_print(await ovh_api.delete_an_email_account(args[1], args[2]))
        return
    if len(args) >= 1 and args[0] == "list-email-redirections":
        raise NotImplementedError("code not verified")  # list_email_redirections
    if len(args) >= 1 and args[0] == "create-a-redirection":
        raise NotImplementedError("code not verified")  # create_a_redirection
    if len(args) >= 1 and args[0] == "check-domain-quota-usage":
        raise NotImplementedError("code not verified")  # check_domain_quota_usage
    if len(args) >= 1 and args[0] == "get-service-information":
        raise NotImplementedError("code not verified")  # get_service_information
    if len(args) >= 1 and args[0] == "check-if-you-can-order-additional-resources":
        raise NotImplementedError("code not verified")  # check_if_you_can_order_additional_resources
    help_list = [
        ["list", "", "list_all_email_domains"],
        ["list", " domain", "list_email_accounts_for_a_domain"],
        ["info", "", "get_details_for_a_specific_domain"],
        ["info", " account-name", "get_account_details"],
        ["create-account", " domain account-name password description size-in-bytes", "create_a_new_email_account"],
        ["update-account-quota", " domain-name account-name size-in-bytes", "update_account_quota"],
        ["delete-account", " domain-name account-name", "delete_an_email_account"],
        ["list-redirections", "", "list_email_redirections"],
        ["create-redirection", "", "create_a_redirection"],
        ["check-quota", "", "check_domain_quota_usage"],
        ["get-service-information", "", "get_service_information"],
        ["upgrade-availables", "", "check_if_you_can_order_additional_resources"],
    ]
    DIM, WHITE, PURP = Color.DIM.value, Color.WHITE.value, Color.PURP.value
    print(
        "HELP\n"
        + "\n".join(
            f" {DIM}- {PURP}cloud ovh email {WHITE}{name}{PURP}{arguments}{DIM} - {description}"
            for name, arguments, description in help_list
        )
    )


async def ovh_telephony(ovh_api, args):
    if args == ["list"]:
        billing_accounts = await ovh_api.list_telephony_services()
        print(f"{Color.PURP.value}Telephony billing accounts:{Color.WHITE.value}")
        for account in billing_accounts:
            print(f"{Color.DIM.value} - {Color.WHITE.value}{account}")
        return

    if len(args) == 2 and args[0] == "voicemail":
        voicemail_services = await ovh_api.list_voicemail_services(args[1])
        print(f"{Color.PURP.value}Voicemail services for {args[1]}:{Color.WHITE.value}")
        for service in voicemail_services:
            print(f"{Color.DIM.value} - {Color.WHITE.value}{service}")
        return

    if len(args) == 4 and args[0] == "voicemail" and args[3] == "list":
        messages = await ovh_api.list_voicemail_messages(args[1], args[2])
        print(f"{Color.PURP.value}Voicemail messages for {args[1]}/{args[2]}:{Color.WHITE.value}")
        for message in messages:
            print(f"{Color.DIM.value} - Message ID: {Color.WHITE.value}{message}")
        return

    if len(args) == 5 and args[0] == "voicemail" and args[4] == "details":
        details = await ovh_api.get_voicemail_message_details(args[1], args[2], args[3])
        print(f"{Color.PURP.value}Message details:{Color.WHITE.value}")
        pretty_print(details)
        return

    if len(args) >= 5 and args[0] == "voicemail" and args[4] == "download":
        audio_format = "wav"
        if len(args) == 6:
            audio_format = args[5]

        audio_data = await ovh_api.download_voicemail_message(args[1], args[2], args[3], audio_format)
        filename = f"voicemail_{args[1]}_{args[2]}_{args[3]}.{audio_format}"

        with Path(filename).open("wb") as f:
            f.write(audio_data)

        print(f"{Color.GREEN.value}Downloaded voicemail message to {filename}{Color.WHITE.value}")
        return

    if len(args) >= 5 and args[0] == "voicemail" and args[4] == "download-greeting":
        audio_format = "wav"
        if len(args) == 6:
            audio_format = args[5]

        audio_data = await ovh_api.download_voicemail_greeting(args[1], args[2], args[3], audio_format)
        filename = f"greeting_{args[1]}_{args[2]}_{args[3]}.{audio_format}"

        with Path(filename).open("wb") as f:
            f.write(audio_data)

        print(f"{Color.GREEN.value}Downloaded voicemail greeting to {filename}{Color.WHITE.value}")
        return

    if len(args) == 4 and args[0] == "voicemail" and args[3] == "settings":
        settings = await ovh_api.get_voicemail_settings(args[1], args[2])
        print(f"{Color.PURP.value}Voicemail settings for {args[1]}/{args[2]}:{Color.WHITE.value}")
        pretty_print(settings)
        return

    # Help
    DIM, WHITE, PURP = Color.DIM.value, Color.WHITE.value, Color.PURP.value
    print(
        f"{PURP}TELEPHONY HELP{WHITE}\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}list{DIM} - List billing accounts\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account>{DIM} - List voicemail services\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account> <service> list{DIM} - List messages\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account> <service> <msg-id> details{DIM} - Get message details\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account> <service> <msg-id> download [wav|mp3]{DIM} - Download message\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account> <service> <greeting-id> download-greeting [wav|mp3]{DIM} - Download greeting\n"
        f" {DIM}- {PURP}cloud ovh telephony {WHITE}voicemail <billing-account> <service> settings{DIM} - Get voicemail settings\n"
    )


async def ovh_buy(ovh_api, args):
    def buy_usage():
        options = [
            "start description",
            "assign cart-id",
            "cancel cart-id",
            "view cart-id",
            f"checkout cart-id  {Color.DIM.value}# you must pay after checkout, see orders{Color.WHITE.value}",
            "─",
            "add cart-id domain domain.ovh",
        ]
        print(
            "\n"
            + "\n".join(
                "─" * 40 if option == "─" else f"{Color.DIM.value}- {Color.WHITE.value}cloud ovh buy {option}"
                for option in options
            )
            + "\n"
        )
        return -1

    # Start
    if len(args) == 2 and args[0] == "start":
        return await ovh_api.create_cart(args[1])
    # Cancel
    if len(args) == 2 and args[0] == "cancel":
        return await ovh_api.cancel_cart(args[1])
    # View
    if len(args) == 2 and args[0] == "view":
        response = await ovh_api.get_cart_checkout_infos(args[1])
        pretty_print(response)
        return
    # Assign
    if len(args) == 2 and args[0] == "assign":
        return await ovh_api.assign_cart(args[1])
    # Checkout
    if len(args) == 2 and args[0] == "checkout":
        response_view = await ovh_api.get_cart_checkout_infos(args[1])
        pretty_print(response_view)
        confirm("Will accept these terms, and will checkout. ")
        response_checkout = await ovh_api.checkout_cart(args[1])
        pretty_print(response_checkout)
        print(f"{Color.RED.value}WARNING you must now pay using {Color.WHITE.value}cloud ovh orders")
        return
    # Domain - add
    if len(args) == 4 and args[0] == "add" and args[2] == "domain":
        response = await ovh_api.add_domain_to_cart(domain_name=args[3], cart_id=args[1])
        pretty_print(response)
        return None
    return buy_usage()


async def ovh_orders(ovh_api, args):
    # Pay
    if args == ["list"]:
        response = await ovh_api.list_orders()
        pretty_print(response)
        return
    if len(args) == 3 and args[0] == "pay":
        print(f"\n    {Color.RED.value}WARNING CREDIT_CARD was refused for domains{Color.WHITE.value}\n")
        response_pay = await ovh_api.pay_order(order_id=args[1], payment_method_id=args[2])
        pretty_print(response_pay)
        return
    print("\n-cloud ovh orders list")
    print("\n-cloud ovh orders pay order-id payment-method-id")
    return


async def ovh_payment(ovh_api, args):
    pretty_print(await ovh_api.get_payment_methods())
    return


async def scaleway_domain(scaleway_api, args):
    if args == ["list"]:
        pretty_print(await scaleway_api.list_domains())
        return
    if len(args) == 2 and args[0] == "get":
        pretty_print(await scaleway_api.get_domain(args[1]))
        return
    print("- cloud scaleway domain list\n- cloud scaleway domain get project_id")


async def scaleway_invoice(scaleway_api, scaleway_config):
    if not scaleway_config.invoice_path:
        raise CloudException("Missing 'invoice-path' in Scaleway config (use {year} and {invoice_id} placeholders)")
    invoices = await scaleway_api.list_invoices()
    downloaded_count = 0
    for invoice in invoices:
        invoice_id = invoice["id"]
        if not isinstance(invoice["issued_date"], str):
            raise CloudException(f"Invalid type for date of invoice {invoice_id}")
        invoice_short_date = invoice["issued_date"][:10]
        invoice_year = invoice_short_date[:4]
        if len(invoice_year) != 4 or not all(c in "0123456789" for c in invoice_year):
            raise CloudException(f"Unexpected date format for invoice {invoice_id}: {invoice['issued_date']}")
        pdf_path = Path(
            scaleway_config.invoice_path.format(
                year=invoice_year, invoice_id=invoice_id, printable_date=invoice_short_date
            )
        )
        pdf_path_tmp = Path(f"{pdf_path}.tmp")
        if not pdf_path.exists():
            print(f"Downloading {invoice_id} for {invoice_short_date}")
            downloaded_pdf_name, downloaded_pdf_content = await scaleway_api.get_invoice_pdf(invoice_id)
            print(f"=> Writing {pdf_path_tmp}")
            with pdf_path_tmp.open("wb") as f:
                f.write(downloaded_pdf_content)
            with pdf_path_tmp.open("rb") as f:
                verif_pdf_content = f.read()
            if not verif_pdf_content.startswith(b"%PDF-1.") or verif_pdf_content != downloaded_pdf_content:  # paranoid
                raise CloudException(f"Error on invoice save: check {pdf_path_tmp}")
            pdf_path_tmp.rename(pdf_path)
            print(f"=> Validated and moved to {pdf_path}")
            downloaded_count += 1
    print(f"Downloaded {downloaded_count}/{len(invoices)} invoices")


async def scaleway_servers(scaleway_api):
    server_dict = await scaleway_api.list_servers()
    if type(server_dict) is not dict or len(server_dict) != 1 or type(server_dict.get("servers")) is not list:
        raise CloudException("Invalid data structures when listing servers")
    for server in server_dict["servers"]:
        print(f"{server.get('id', '')} - {server.get('name', '').ljust(30)} - {server.get('commercial_type', '')}")


async def scaleway_remove_server(scaleway_api, server_id):
    print("WILL MAKE A DELETE ON THE RESOURCE, CHECK THE ACTUAL IMPLICATIONS")
    confirm(f"Will wipe server {server_id}. ")
    response_dict = await scaleway_api.remove_server(server_id)
    print(response_dict)


async def scaleway_terminate_server(scaleway_api, server_id):
    confirm(f"Will wipe server {server_id}. ")
    response_dict = await scaleway_api.terminate_server(server_id)
    print(response_dict)


async def main():
    ovh_config, scaleway_config = load_config()
    if not ovh_config or not scaleway_config:
        return usage()  # TODO Better to show config
    help_items = []  # will be populated by either scaleway or ovh main help
    ovh_api = OVHApi(
        cert_checksum=ovh_config.certificate,
        pdf_cert_checksum=ovh_config.pdf_certificate,
        application_key=ovh_config.application_key,
        application_secret=ovh_config.application_secret,
        consumer_key=ovh_config.consumer_key,
    )
    scaleway_api = ScalewayApi(
        cert_checksum=scaleway_config.certificate,
        secret_key=scaleway_config.secret_key,
        organization_id=scaleway_config.organization_id,
    )
    if len(argv) < 2 or argv[1] not in ["ovh", "scaleway"]:
        return usage()
    if argv[1] == "ovh":
        if len(argv) > 2 and argv[2] == "invoice":
            return await ovh_invoice(ovh_api, ovh_config)
        if len(argv) > 2 and argv[2] == "vps":
            return await ovh_vps(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "domain":
            return await ovh_domain(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "email":
            return await ovh_email(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "dedicated-server":
            if len(argv) == 5 and argv[3] == "monitor-reinstall":
                return await ovh_servers_monitor_reinstall(ovh_api, argv[4])
            if len(argv) == 6 and argv[3] == "reinstall":
                return await ovh_servers_reinstall(ovh_api, argv[4], argv[5])
            if len(argv) == 3:
                return await ovh_servers(ovh_api)
            print("cloud ovh dedicated-server")
            print("cloud ovh dedicated-server reinstall XXX SSH_KEY")  # SSH_KEY not name
            print("cloud ovh dedicated-server monitor-reinstall XXX")
            return
        if len(argv) > 2 and argv[2] == "ssh-key":
            return await ovh_ssh_keys(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "buy":
            return await ovh_buy(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "orders":
            return await ovh_orders(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "payment":
            return await ovh_payment(ovh_api, argv[3:])
        if len(argv) > 2 and argv[2] == "telephony":
            return await ovh_telephony(ovh_api, argv[3:])
        help_items = [
            "ovh vps",
            "ovh invoice",
            "ovh dedicated-server",
            "ovh ssh-key",
            "ovh domain",
            "ovh email",
            f"ovh telephony {Color.DIM.value}# voicemail messages{Color.WHITE.value}",
            f"ovh buy       {Color.DIM.value}# manage carts{Color.WHITE.value}",
            f"ovh orders    {Color.DIM.value}# manage orders (checked out carts have to be paid with this)",
            f"ovh payment   {Color.DIM.value}# list payment methods{Color.WHITE.value}",
        ]
    else:
        if len(argv) > 2 and argv[2] == "invoice":
            return await scaleway_invoice(scaleway_api, scaleway_config)
        if len(argv) > 2 and argv[2] == "domain":
            return await scaleway_domain(scaleway_api, argv[3:])
        if len(argv) > 2 and argv[2] == "server":
            if len(argv) == 3:
                return await scaleway_servers(scaleway_api)
            if len(argv) == 5 and argv[3] == "terminate":
                return await scaleway_terminate_server(scaleway_api, argv[4])
            if len(argv) == 5 and argv[3] == "remove":
                return await scaleway_remove_server(scaleway_api, argv[4])
            print("cloud scaleway server")
            print("cloud scaleway server terminate {server_id}  === Wipes attached storages")
            print("cloud scaleway server remove {server_id}     === Makes a delete - ?")
            return
        help_items = [
            "scaleway domain",
            "scaleway server",
            "scaleway invoice",
        ]
    print(
        f"\n{Color.PURP.value}Select a category{Color.WHITE.value}\n"
        + "\n".join(f"{Color.DIM.value} - {Color.WHITE.value}cloud {item}" for item in help_items)
        + "\n"
    )


if __name__ == "__main__":
    try:
        exit(asyncio_run(main()))
    except KeyboardInterrupt:
        print("\n  !!  KeyboardInterrupt received  !!  \n")
        exit(-2)
    except CloudException as e:
        print(f"{Color.RED.value}\n  !!  {e}  !!  \n{Color.WHITE.value}")
        exit(-1)
    except Exception:
        raise
