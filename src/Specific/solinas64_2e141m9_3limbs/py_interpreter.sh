#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**141 - 9' -Dmodulus_bytes='47' -Da24='121665'
