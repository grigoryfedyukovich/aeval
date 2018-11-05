extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int N;
  int a[N];
  int b[N];
  int x;

  for (int i = 0; i < N; i++) {
    x = __VERIFIER_nondet_int();
    a[i] = x;
    b[i] = -x;
  }

  for (int i = 0; i < N; i++) {
    a[i] = -1*b[i];
    b[i] = a[i];
  }

  for (int i = 1; i < N; i++)
    __VERIFIER_assert(a[i] == b[i]);

  return 0;
}
