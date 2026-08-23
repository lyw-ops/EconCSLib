# R000 fixtures

R000 adds no copied Gold, candidate, or mutation fixture. The replay reads the
tracked Stage 2 accepted sources and `mutations.json` without changing them,
then materializes disposable candidate trees under a system temporary
directory. This directory exists to make that no-copy policy explicit and to
reserve a reviewed location for future rubric-only fixtures.

Do not place hidden evaluation material, DEV-003 runtime candidates, model
outputs, textbook scans, or answer-revealing private assets here.
