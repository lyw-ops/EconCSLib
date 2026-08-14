# v0.3.0 JSON Schemas

This directory contains the complete set of 11 JSON Schema Draft 2020-12 files
from the supplied `mathlib_style_v0.3.0 3` artifact. They were copied verbatim;
no schema IDs, references, fields, or validation semantics were changed.

[`MANIFEST.json`](MANIFEST.json) records the byte count and SHA-256 copied from
the artifact's `MANIFEST_v0.3.0.json`. The repository checker verifies the exact
file set, byte counts, hashes, JSON parsing, Draft 2020-12 declarations, unique
schema IDs, and resolution of every local `$ref` target.

These schemas describe the frozen formal benchmark formats: task-specific and
public cases, private gold and provenance, predictions, annotations, and
validation records. The public synthetic smoke fixtures use repository
integration metadata and are not presented as formal cases conforming to the
legacy public-case union.
