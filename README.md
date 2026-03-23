# cloud

KISS cli to interact with french cloud providers (OVH + Scaleway) — zero dependencies, stdlib only.

Started as some curls to grab invoices and poke at server infos... then this monstrosity materialized into existence.
Single file, no `requests`, no `click`, no `boto3` — just `urllib`, `ssl`, and `asyncio` doing their best.

### What it does
- **OVH**: VPS, dedicated servers, domains/DNS, email, telephony/voicemail, invoices, carts, orders, payments
- **Scaleway**: servers, domains, invoices

### What it cares about
- TLS certificate pinning on every request
- Paranoid input validation before anything touches a URL
- Parallel API calls via `asyncio.gather`
- Atomic writes for invoice PDF downloads

### Disclaimer
I don't recommend using this as-is — this is a PoC, usable by me because I know what I want to do with it.
You can use it if you feel that you can edit the code yourself and you can live with my future breaking changes.

For more polished work, see my [list of projects](https://github.com/c4ffein/c4ffein/blob/main/REPOS.md). And I do use Terraform in big companies. Else, this is how I configure servers for some of my toy projects <3
