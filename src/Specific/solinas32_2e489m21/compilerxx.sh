#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='27' -Dmodulus_bytes_val='18 + 1/9' -Dlimb_t=uint32_t -Dlimb_weight_gaps_array='{19,18,18,18,18,18,18,18,18,19,18,18,18,18,18,18,18,18,19,18,18,18,18,18,18,18,18}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xeb}' -Dq_mpz='(1_mpz<<489) - 21' "$@"