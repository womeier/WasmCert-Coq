"""Shared byte encoders for independent binary runtime fixtures."""


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def vector(items):
    return uleb(len(items)) + b"".join(items)


def section(tag, payload):
    return bytes([tag]) + uleb(len(payload)) + payload


def escaped(data):
    return '"' + "".join(f"\\{b:02x}" for b in data) + '"'
