#!/usr/bin/env zsh

set -xe

OUT_DIR=gen_output
BENCH_DIR=gen_output/benchmarks

rm -rf $OUT_DIR
mkdir -p $BENCH_DIR

csv_path="$OUT_DIR/benchmarks.csv"

touch $csv_path

echo "ty,drop,bits,vars,terms,seed,op,theory,toolchain,file" >> $csv_path

for vars in $(seq 2 2 20); do
    for op in and or; do
        for bits in 255; do
            for theory in ff bv; do
                for drop in none last random; do
                    for ty in sound deterministic; do
                        for toolchain in circ zokref zokcirc; do
                            seed=0
                            terms=0
                            cargo run --release -- \
                                --terms $terms \
                                --vars $vars \
                                -t $toolchain \
                                --logic $theory \
                                --field-bits $bits \
                                --ty $ty \
                                --drop $drop \
                                --seed $seed \
                                --gen-nary $op \
                                -o xor \
                                --no-consts \
                                --circ-opt \
                                --circ-opt-r1cs
                            name="compilation-$ty-$drop-${(l(2)(0))vars}v-${(l(3)(0))terms}t-$theory-$toolchain-${bits}b-${op}s.smt2"
                            echo "$ty,$drop,$bits,$vars,$terms,$seed,$op,$theory,$toolchain,$name" >> $csv_path
                            mv out.smt2 $BENCH_DIR/$name
                        done
                    done
                done
            done
        done
    done
done

for vars in 2 4 6 8 10 12; do
    for terms in 1 2 4 8 16 32 64 128; do
        for bits in 255; do
            for theory in ff nia bv pureff; do
                for drop in none last random; do
                    for ty in sound deterministic; do
                        for toolchain in circ zokref zokcirc; do
                            seed=0
                            op=random
                            cargo run --release -- \
                                --terms $terms \
                                --vars $vars \
                                -t $toolchain \
                                --logic $theory \
                                --field-bits $bits \
                                --ty $ty \
                                --drop $drop \
                                --seed $seed \
                                -o xor \
                                --no-consts \
                                --circ-opt \
                                --circ-opt-r1cs
                            name="compilation-$ty-$drop-${(l(2)(0))vars}v-${(l(3)(0))terms}t-$theory-$toolchain-${bits}b-${seed}s.smt2"
                            echo "$ty,$drop,$bits,$vars,$terms,$seed,$op,$theory,$toolchain,$name" >> $csv_path
                            mv out.smt2 $BENCH_DIR/$name
                        done
                    done
                done
            done
        done
    done
done

for vars in 2; do
    for terms in 4; do
        for bits in 4 5 6 7 8 9 10 11 12; do
            for theory in ff; do
                for drop in none last random; do
                    for ty in sound deterministic; do
                        for toolchain in circ zokref zokcirc; do
                            seed=0
                            op=random
                            cargo run --release -- \
                                --terms $terms \
                                --vars $vars \
                                -t $toolchain \
                                --logic $theory \
                                --field-bits $bits \
                                --ty $ty \
                                --drop $drop \
                                --seed $seed \
                                -o xor \
                                --no-consts \
                                --circ-opt \
                                --circ-opt-r1cs
                            name="compilation-$ty-$drop-${(l(2)(0))vars}v-${(l(3)(0))terms}t-$theory-$toolchain-${bits}b-${seed}s.smt2"
                            echo "$ty,$drop,$bits,$vars,$terms,$seed,$op,$theory,$toolchain,$name" >> $csv_path
                            mv out.smt2 $BENCH_DIR/$name
                        done
                    done
                done
            done
        done
    done
done

for vars in 4; do
    for terms in 8; do
        for bits in 5 10 15 20 25 30 35 40 45 50 55 60; do
            for theory in ff bv; do
                for drop in none last random; do
                    for ty in sound deterministic; do
                        for toolchain in circ zokref zokcirc; do
                            seed=0
                            op=random
                            cargo run --release -- \
                                --terms $terms \
                                --vars $vars \
                                -t $toolchain \
                                --logic $theory \
                                --field-bits $bits \
                                --ty $ty \
                                --drop $drop \
                                --seed $seed \
                                -o xor \
                                --no-consts \
                                --circ-opt \
                                --circ-opt-r1cs
                            name="compilation-$ty-$drop-${(l(2)(0))vars}v-${(l(3)(0))terms}t-$theory-$toolchain-${bits}b-${seed}s.smt2"
                            echo "$ty,$drop,$bits,$vars,$terms,$seed,$op,$theory,$toolchain,$name" >> $csv_path
                            mv out.smt2 $BENCH_DIR/$name
                        done
                    done
                done
            done
        done
    done
done

