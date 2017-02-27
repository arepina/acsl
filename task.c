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

/*@ axiomatic MaxInd{
 logic integer max_ind{L}(int *a, unsigned n);

 axiom a1:
    \forall int *a, unsigned n; 0 <= max_ind(a, n) <= n;
 axiom a2:
    \forall int *a, unsigned n, integer i; 0 <= i < n ==> a[i] <= a[max_ind(a,n)];
 }
*/

/*@ axiomatic Cnt {
     logic integer Count{L}(int* a, integer n, int v);

     predicate Permutation{L1,L2}(int *a, integer n) =
        \forall int v; Count{L1}(a, n, v) == Count{L2}(a, n, v);

     axiom CountEmpty:
        \forall int *a, v, integer n;
           n <= 0 ==> Count(a, n, v) == 0;
          axiom CountOneHit:
        \forall int *a, v, integer n;
                     n > 0 && a[n - 1] == v ==> Count(a, n, v) == Count(a, n - 1, v) + 1;

     axiom CountOneMiss:
        \forall int *a, v, integer n; n > 0 && a[n - 1] != v ==> Count(a, n, v) == Count(a, n - 1, v);

     lemma SwapImmutability{L1,L2}:
        \forall int *a, integer n, i, j; 0 <= i < n && 0 <= j < n && Swap{L1,L2}(a, i, j, n) ==> Permutation{L1,L2}(a, n);

     lemma Validity{L1}:
        \forall int* a, int n; (n > 0 && \forall integer k; 0 <= k < n ==> \at(\valid(a+k), L1)) ==> Permutation{L1, L1}(a, n);
    }
*/

//@ ghost int size_b = 5;
/*@
    requires size_a % 2 == 0;
    requires \valid(a + (0..size_a-1));
    requires \valid(b + (0..max_ind(a, size_a)));
    requires \forall integer k; 0 <= k < size_a ==> a[k] < size_b;
    requires \forall integer k; 0 <= k < size_a ==> a[k] >= 0;
    requires \exists integer mx; 0 <= mx < size_a && (\forall integer k; 0 <= k < size_a ==> a[k] <= a[mx]) && \valid(b + (0..a[mx]));
    ensures Permutation{Pre,Here}(b, size_b);
    ensures unchanged: Unchanged{Pre,Here}(a, size_a);
 */
void task(int a[], int b[], unsigned size_a) {
    /*@
      loop assigns i, b;
      loop invariant bound: 0 <= i <= size_a + 1;
      loop invariant i % 2 == 0;
      loop invariant Permutation{Pre, Here}(b, size_b);
      loop variant size_a - i;
   */
    for (unsigned i = 0; i < size_a; i += 2) {
        int tmp = b[a[i]];
        b[a[i]] = b[a[i + 1]];
        b[a[i + 1]] = tmp;
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
