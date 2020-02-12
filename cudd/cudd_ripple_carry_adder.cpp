#include <chrono>

#include "util.h"
#include "cudd.h"

void bench(int num_vars) {
    int repeat = 100;
    long int total = 0;
    for (int r = 0; r < repeat; r++) {
        auto start = std::chrono::high_resolution_clock::now();
        DdManager *gbm;
        gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

        // for some reason, Cudd_ReadZero is doing som bullshit
        DdNode *bdd = Cudd_bddAnd(gbm, Cudd_bddIthVar(gbm,0), Cudd_Not(Cudd_bddIthVar(gbm,0)));
        Cudd_Ref(bdd);

        for (int i = 0; i < (num_vars / 2); i++) {
            DdNode *var1 = Cudd_bddIthVar(gbm,i);
            DdNode *var2 = Cudd_bddIthVar(gbm,i + (num_vars / 2));
            DdNode *tmp_and = Cudd_bddAnd(gbm, var1, var2);
            DdNode *tmp_or = Cudd_bddOr(gbm, tmp_and, bdd);
            Cudd_Ref(tmp_or);
            Cudd_RecursiveDeref(gbm,bdd);
            bdd = tmp_or;
        }
        Cudd_Quit(gbm);
        auto finish = std::chrono::high_resolution_clock::now();
        long int duration = std::chrono::duration_cast<std::chrono::nanoseconds>(finish-start).count();
        total = total + duration;
        printf("\r%d...", r);
        fflush(stdout);
    }
    printf("\rcudd_ripple_carry_adder_%d: %ld (ns)\n", num_vars, total / repeat);
}

int main (int argc, char *argv[])
{
    bench(4);
    bench(8);
    bench(16);
    bench(32);
}