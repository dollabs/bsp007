#!/bin/sh
#
# Copyright © 2016 Dynamic Object Language Labs Inc.
#
# This software is licensed under the terms of the
# Apache License, Version 2.0 which can be found in
# the file LICENSE at the root of this distribution.

# Acknowledgement and Disclaimer:
# This material is based upon work supported by the Army Contracting
# and DARPA under contract No. W911NF-15-C-0005.
# Any opinions, findings and conclusions or recommendations expressed
# in this material are those of the author(s) and do necessarily reflect the
# views of the Army Contracting Command and DARPA.

dir=$(dirname $0)
set -e

# Build an attack plan

java -jar $CODE/target/dmcgp.jar -s 1000 -v 0 \
         -g $CODE/test/planner/${NUMBER}_dcrypps2test.ir.json -G AttackPlanner \
         -o "$RESULTS/${NUMBER}_dcrypps2test.plan" -T 1\
         make-plan

if ! diff -u "$dir/${NUMBER}_dcrypps2test.good" "$RESULTS/${NUMBER}_dcrypps2test.plan";
then
  exit 1
fi
