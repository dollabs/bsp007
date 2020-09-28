dmcgp.sh -s 10 -v 0 -g tests/simple.ir.json -G world -o tests/output/simple.out make-plan
dmcgp.sh -s 100 -v 0 -g tests/plannertest.ir.json -G world -o tests/output/plannertest.out make-plan
dmcgp.sh -s 1000 -v 0 -g tests/dcryppstest.ir.json -G AttackPlanner -o tests/output/dcryppstest.out make-plan
