/*@ predicate Unchanged{K,L}(int* a, integer first, integer last) =
        \forall integer i; first <= i < last ==>
        \at(a[i],K) == \at(a[i],L);

    predicate Unchanged{K,L}(int* a, integer n) = Unchanged{K,L}(a, 0, n);

    lemma UnchangedStep{K,L}:
        \forall int *a, integer n; 0 <= n ==> Unchanged{K,L}(a, n) ==>
        \at(a[n],K) == \at(a[n],L) ==> Unchanged{K,L}(a, n+1);

    lemma UnchangedSection{K,L}:
        \forall int *a, integer m, n; 0 <= m <= n ==> Unchanged{K,L}(a, n)
        ==> Unchanged{K,L}(a, m);
*/

/*@ predicate Swap{L1,L2}(int *a, integer i, integer j, integer size) =
       \at(a[i],L1) == \at(a[j],L2) &&
       \at(a[j],L1) == \at(a[i],L2) &&
       \forall integer k; 0 <= k < size && k != i && k != j
          ==> \at(a[k],L1) == \at(a[k],L2);
 */


/*@ axiomatic MaxInd {
    logic integer max_ind{L}(int *b, unsigned size) reads b[0..size-1];
    axiom a1{L}:
       \forall int *b, unsigned size; size > 0 ==> 0 <= max_ind(b, size) < size;

    axiom a2{L}:
       \forall int *b, unsigned size, i; 0 <= i < size ==> b[i] <= b[max_ind(b, size)];

    lemma l1{L}:
       \forall int *b, unsigned size; size > 0 ==> \exists integer i; 0 <= i < size && i == max_ind(b, size);

    lemma l2{L}:
       \forall int *b, unsigned size; size > 0 ==> \exists integer i; 0 <= i < size && b[i] == b[max_ind(b, size)];

    lemma l3{L}:
       \forall int *b, unsigned size, i; 0 <= i < size ==> b[i] <= b[max_ind(b, size)];
    }
 */


/*@ axiomatic Permut {
    // Permut{L1,L2}(t1, t2, n) is true whenever t1[0..n-1] in state L1 is a permut of t2[0..n-1] in state L2

    predicate Permut{L1, L2}(int *t1, int *t2, integer n);

    axiom Permut_refl{L}:
        \forall int *t, integer n; Permut{L, L}(t, t, n);

    axiom Permut_sym{L1 ,L2} :
        \forall int *t1 , *t2, integer n;
        Permut{L1,L2}(t1, t2, n) ==> Permut{L2,L1}(t2, t1, n);

    axiom Permut_trans{L1 ,L2 ,L3} :
        \forall int *t1 , *t2, *t3, integer n;
        Permut{L1, L2}(t1, t2, n) && Permut{L2, L3}(t2, t3, n)
        ==> Permut{L1, L3}(t1, t3, n);

    axiom Permut_exchange{L1,L2} :
        \forall int *t1 , *t2, integer i, j, n;
        \at (t1[i],L1) == \at (t2[j],L2) &&
        \at (t1[j],L1) == \at (t2[i],L2) &&
        (\forall integer k; 0 <= k < n && k != i && k != j ==> \at (t1[k],L1) == \at (t2[k],L2)) ==> Permut{L1,L2}(t1 ,t2 ,n);

    lemma SwapImmutability{L1,L2}:
        \forall int *a, int n, i, j; (0 <= i < n && 0 <= j < n && Swap{L1,L2}(a, i, j, n)) ==> Permut{L1,L2}(a, a, n);

    lemma Validity{L1}:
        \forall int* a, int n; (n > 0 && \forall integer k; 0 <= k < n ==> \at(\valid(a+k), L1)) ==> Permut{L1, L1}(a, a, n);
 }
*/

/*@ predicate CheckTask{L1,L2}(int* a, int* b, integer n) =
        \forall integer i; 0 <= i < n && i % 2 == 0
        ==> (\at(b[a[i]], L1) == \at(b[a[i + 1]], L2))
        && (\at(b[a[i + 1]], L1) == \at(b[a[i]], L2));
 */

//@ ghost unsigned size_b = 5;
/*@
    requires size_a % 2 == 0;
    requires size_b == max_ind(a, size_a);
    requires \valid(a + (0..size_a-1));
    requires \valid(b + (0..size_b));
    requires \forall integer k; 0 <= k < size_a ==> a[k] < size_b;
    requires \forall integer k; 0 <= k < size_a ==> a[k] >= 0;
    requires \exists integer mx; 0 <= mx < size_a && (\forall integer k; 0 <= k < size_a ==> a[k] <= a[mx]) && \valid(b + (0..a[mx]));
    assigns b[0..size_b-1];
    ensures Permut{Pre,Here}(b, b, size_b);
    ensures unchanged: Unchanged{Pre,Here}(a, size_a);
    ensures CheckTask{Pre, Here}(a, b, size_a);
 */
void task(int a[], int b[], unsigned size_a) {
    /*@
      loop assigns b[0..size_b-1];
      loop invariant bound: 0 <= i <= size_a;
      loop invariant i % 2 == 0;
      loop invariant \forall integer k, integer h; 0 <= k <= i && 0 <= h < size_b && h != a[k]  ==> \at(b[h], Pre) == \at(b[h], Here);
      loop invariant CheckTask{Pre, Here}(a, b, i);
      loop invariant Permut{Pre, Here}(b, b, size_b);
      loop variant size_a - i;
   */
    for (unsigned i = 0; i < size_a; i += 2) {
        //@ghost Before:
        int tmp = b[a[i]];
        b[a[i]] = b[a[i + 1]];
        b[a[i + 1]] = tmp;
        //@ assert \at(b[a[i]], Before) == \at(b[a[i + 1]], Here);
        //@ assert \at(b[a[i + 1]], Before) == \at(b[a[i]], Here);
        //@ assert Swap{Before, Here}(b, a[i], a[i + 1], size_b);
    }
}


#ifdef OUT_OF_TASK
#include <stdio.h>

int main(void)
{
    unsigned n = 6;
    int a[] = {0, 1, 1, 2, 3, 4};
    int b[] = {1, 2, 3, 4, 5};
    task(a, b, n);
    for(int i = 0; i < 5; ++i)
        printf("%d \n", b[i]);
    return 0;
}

#endif
