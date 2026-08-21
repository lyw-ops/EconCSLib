# StructuralCore usability guidance

Treat `Arena.Reachable` as an endpoint-existence proposition and
`Arena.History` as a concrete dependent action occurrence. A proof that an
endpoint is reachable may justify a nonempty history type, but proof
irrelevance means reachability proof objects cannot encode which route was
taken. `Arena.HistoryFrom` bundles an endpoint with one concrete history and is
the appropriate carrier when merged world states must remain separate
occurrences.

Start from the single imported facade and search the declarations it already
exposes before attempting an induction. Prefer a direct use of an existing
bridge or projection when its type exactly matches the task. For a local
merged-state regression, prove facts about the two supplied history values;
do not change the arena, add a core declaration, or assert an inverse between
proof-irrelevant reachability and occurrence-sensitive histories.

Compilation is necessary but not sufficient. Preserve the fixed task prefix,
keep the exact declaration types, inspect warnings, and avoid all placeholders,
new trusted declarations, native trust shortcuts, or linter suppression.
