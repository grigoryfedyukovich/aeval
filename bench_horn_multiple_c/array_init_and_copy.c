extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int N;
  int a[N];
  int b[N];

  for (int i = 0; i < N; i++)
    a[i] = 1;

  for (int i = 0; i < N; i++)
    b[i] = a[i];

  for (int i = 1; i < N; i++)
    __VERIFIER_assert(b[i] >= 1);

  return 0;
}
