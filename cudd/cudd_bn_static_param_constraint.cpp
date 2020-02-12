#include <chrono>

#include "util.h"
#include "cudd.h"

void bench_observability(int num_regulators) {
    int repeat = 100;
    int num_vars = 1 << num_regulators;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();
        DdManager *gbm;
        gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

        // for some reason, Cudd_ReadZero is doing som bullshit
        DdNode *bdd = Cudd_ReadOne(gbm);
        Cudd_Ref(bdd);

        for (int input=0; input < num_regulators; input++) {
            int block_size = 1 << (input + 1);
            int half_block = block_size / 2;
            // fake zero...
            DdNode *regulator_formula = Cudd_bddAnd(gbm, Cudd_bddIthVar(gbm,0), Cudd_Not(Cudd_bddIthVar(gbm,0)));
            for (int block=0; block < (num_vars / block_size); block++) {
                for (int block_item=0; block_item < half_block; block_item++) {
                    DdNode *var1 = Cudd_bddIthVar(gbm, block_size * block + block_item);
                    DdNode *var2 = Cudd_bddIthVar(gbm, block_size * block + block_item + half_block);
                    DdNode *tmp = Cudd_Not(Cudd_bddOr(gbm, Cudd_bddAnd(gbm, var1, var2), Cudd_bddAnd(gbm, Cudd_Not(var1), Cudd_Not(var2))));
                    DdNode *tmp_r = Cudd_bddOr(gbm, regulator_formula, tmp);
                    Cudd_Ref(tmp_r);
                    Cudd_RecursiveDeref(gbm, regulator_formula);
                    regulator_formula = tmp_r;
                }
            }
            DdNode *tmp = Cudd_bddAnd(gbm, regulator_formula, bdd);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(gbm, bdd);
            bdd = tmp;
        }

        Cudd_Quit(gbm);
        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rcudd_bn_parametrised_observability_%d: %ld (ns)\n", num_regulators, total / repeat);
}

void bench_activation(int num_regulators) {
    int repeat = 100;
    int num_vars = 1 << num_regulators;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();
        DdManager *gbm;
        gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

        // for some reason, Cudd_ReadZero is doing som bullshit
        DdNode *bdd = Cudd_ReadOne(gbm);
        Cudd_Ref(bdd);

        for (int input=0; input < num_regulators; input++) {
            int block_size = 1 << (input + 1);
            int half_block = block_size / 2;
            // fake zero...
            DdNode *regulator_formula = Cudd_ReadOne(gbm);
            for (int block=0; block < (num_vars / block_size); block++) {
                for (int block_item=0; block_item < half_block; block_item++) {
                    DdNode *var1 = Cudd_bddIthVar(gbm, block_size * block + block_item);
                    DdNode *var2 = Cudd_bddIthVar(gbm, block_size * block + block_item + half_block);
                    DdNode *tmp = Cudd_bddOr(gbm, Cudd_Not(var1), var2);
                    DdNode *tmp_r = Cudd_bddAnd(gbm, regulator_formula, tmp);
                    Cudd_Ref(tmp_r);
                    Cudd_RecursiveDeref(gbm, regulator_formula);
                    regulator_formula = tmp_r;
                }
            }
            DdNode *tmp = Cudd_bddAnd(gbm, regulator_formula, bdd);
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(gbm, bdd);
            bdd = tmp;
        }

        Cudd_Quit(gbm);
        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rcudd_bn_parametrised_activation_%d: %ld (ns)\n", num_regulators, total / repeat);
}

int main (int argc, char *argv[])
{
    bench_observability(4);
    bench_observability(5);
    bench_activation(4);
    bench_activation(5);
}