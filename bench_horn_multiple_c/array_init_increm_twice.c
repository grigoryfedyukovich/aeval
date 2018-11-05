int main()
{
  int N;
  int a[N];

  for (int i = 0; i < N; i++)
    a[i] = 0;

  for (int i = 0; i < N; i++) {
    a[i] = a[i]+1;
    a[i] = a[i]+1;
  }

  for (int i = 1; i < N; i++)
    assert(a[i] >= 2);

  return 0;
}
