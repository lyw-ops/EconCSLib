#!/usr/bin/env bash
set -eu

: "${EVE_ECONCSLIB_ROOT:?EVE_ECONCSLIB_ROOT is required}"
: "${EVE_SOLVER_ROOT:?EVE_SOLVER_ROOT is required}"
: "${EVE_EVAL_LOG_ROOT:?EVE_EVAL_LOG_ROOT is required}"

python3 "${EVE_ECONCSLIB_ROOT}/experiments/eve/scripts/evaluate_smoke.py" \
  --baseline-dir "${EVE_ECONCSLIB_ROOT}/experiments/eve/smoke/seed" \
  --candidate-dir "${EVE_SOLVER_ROOT}" \
  --score-output "${EVE_EVAL_LOG_ROOT}/score.yaml" \
  --report-output "${EVE_EVAL_LOG_ROOT}/evaluation.json"

