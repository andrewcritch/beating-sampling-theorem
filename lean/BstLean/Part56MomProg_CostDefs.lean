import BstLean.Part56Defs

/-! Stage budgets of the moment program, as functions of the sizes
`N = |Idx n (2dk)|`, `M = |Mono n d|`, `Kc = |KeyRK k d|`. -/

namespace BstLean.Part56.MomProg

/-- One truncated product. -/
def mulCN (N : ℕ) : ℕ := N * (2 * N ^ 2)

def costA (n d M : ℕ) : ℕ := 4 * (n + 1) ^ 2 + 3 * (d + 1) * M
def costB (d N M : ℕ) : ℕ := M * (d * mulCN N)
def costC (d N M : ℕ) : ℕ := 4 * (d + 1) * (N * M) + (M + d + 1) * mulCN N + N * (4 * d + 4)
def costD (k N Kc : ℕ) : ℕ := Kc * (2 * k * mulCN N)
def costE (n d k K N : ℕ) : ℕ :=
  N * ((2 * d * k) ^ (2 * d * k) + (n + 2 * d * k) ^ (2 * d * k) + 2 +
    K * (n + 6 * K + 8 * d * k + 10))
def costF (n d k N Kc : ℕ) : ℕ :=
  Kc * (2 * N + k.factorial + 2 ^ k * k.factorial ^ 2 + n * (n + 1) ^ d + 2 * k + 10)

def costAll (n d k K N M Kc : ℕ) : ℕ :=
  costA n d M + costB d N M + costC d N M + costD k N Kc + costE n d k K N + costF n d k N Kc

end BstLean.Part56.MomProg
