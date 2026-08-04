import base64
import binascii
import hashlib

from . import ChartError


SEALING_PUBLIC_KEY = "vP9uLIF/19VVvLUEZMms8LXJo/RCjRys/Z9S543eG10="

NONCE_BYTES = 24
PUBLIC_KEY_BYTES = 32

GITHUB_TOKEN_PREFIXES = (
    "ghp_",
    "gho_",
    "ghu_",
    "ghs_",
    "ghr_",
    "github_pat_",
)


def require_nacl():
    try:
        from nacl.public import Box, PrivateKey, PublicKey
    except ImportError as error:
        raise ChartError(
            "sealing a token requires PyNaCl; install it with 'pip install pynacl'"
        ) from error
    return Box, PrivateKey, PublicKey


def validate_token(token: str) -> None:
    if token != token.strip():
        raise ChartError("the GitHub token has leading or trailing whitespace")
    if not token.startswith(GITHUB_TOKEN_PREFIXES):
        raise ChartError(
            "the GitHub token must be a personal access token starting with one "
            f"of {', '.join(GITHUB_TOKEN_PREFIXES)}. The workflow seals the token "
            "itself, so store the bare token rather than a pre-sealed one."
        )


def decode_public_key(public_key: str) -> bytes:
    try:
        key = base64.b64decode(public_key, validate=True)
    except (binascii.Error, ValueError) as error:
        raise ChartError(f"the sealing public key is not valid base64: {error}") from error
    if len(key) != PUBLIC_KEY_BYTES:
        raise ChartError(
            f"the sealing public key must be {PUBLIC_KEY_BYTES} bytes, got {len(key)}"
        )
    return key


def seal_token(token: str, public_key: str = SEALING_PUBLIC_KEY) -> str:
    validate_token(token)
    Box, PrivateKey, PublicKey = require_nacl()

    recipient_key = decode_public_key(public_key)
    recipient = PublicKey(recipient_key)
    ephemeral = PrivateKey.generate()
    ephemeral_key = bytes(ephemeral.public_key)

    nonce = hashlib.sha512(ephemeral_key + recipient_key).digest()[:NONCE_BYTES]
    ciphertext = Box(ephemeral, recipient).encrypt(
        token.encode("utf-8"), nonce
    ).ciphertext

    return base64.urlsafe_b64encode(ephemeral_key + ciphertext).decode("ascii").rstrip("=")
