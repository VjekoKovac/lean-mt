#!/usr/bin/env python3
"""Validate the metadata against the pinned upstream v0.4 JSON schema."""
import hashlib
import json
from importlib.metadata import version
from pathlib import Path
from urllib.request import urlopen

import jsonschema
import yaml

COMMIT = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
SCHEMA_URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    f"{COMMIT}/schema/v0.4.schema.json"
)
DIGEST = "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"

with urlopen(SCHEMA_URL, timeout=40) as response:
    schema_bytes = response.read()
if hashlib.sha256(schema_bytes).hexdigest() != DIGEST:
    raise SystemExit("The downloaded schema differs from the reviewed schema.")
root = Path(__file__).resolve().parents[1]
meta = yaml.safe_load((root / "formalization.yaml").read_text())
jsonschema.Draft7Validator(json.loads(schema_bytes)).validate(meta)
if meta["version"] != "v0.4":
    raise SystemExit("This validator checks v0.4.")
print(f"PyYAML {version('PyYAML')}, jsonschema {version('jsonschema')}")
print(f"Upstream schema at commit {COMMIT}, SHA-256 {DIGEST}")
print("PASS: formalization.yaml validates against the upstream v0.4 schema")
