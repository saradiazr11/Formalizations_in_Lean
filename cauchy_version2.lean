import data.real.basic

variable {u : ℕ → ℝ }

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ l, limite u l

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

-- 1ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  unfold suc_cauchy,
  intros ε hε,
  have hε2 : 0 < ε/2 := half_pos hε,
  cases h with l hl,
  cases hl (ε/2) hε2 with N hN,
  clear hε hl hε2,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub l (u q))
   ... < ε/2 + ε/2               : add_lt_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 2ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub l (u q))
   ... < ε/2 + ε/2               : add_lt_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 3ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  have cota1 : |u p - l| < ε / 2 := hN p hp,
  have cota2 : |u q - l| < ε / 2 := hN q hq,
  clear hN hp hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub l (u q)
   ... < ε                       : by linarith,
end

-- 4ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub l (u q)
   ... < ε                       : by linarith [hN p hp, hN q hq],
end

-- 5ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : by simp [abs_add]
   ... = |u p - l|  + |u q - l|  : by simp [abs_sub]
   ... < ε                       : by linarith [hN p hp, hN q hq],
end