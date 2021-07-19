import data.real.basic

variables{u v: ℕ → ℝ }{l a b: ℝ}

notation`|`x`|` := abs x

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def sucesion_cauchy (u : ℕ → ℝ) := 
∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

/-
DEMOSTRACIÓN 1
-/

example : (∃ l, limite u l) → sucesion_cauchy u :=
begin
  intro h,
  unfold sucesion_cauchy,
  intros ε hε,
  have hε2 : 0 < ε/2,
    { linarith },
  cases h with l hl,
  cases hl (ε /2) hε2 with N hN,
  clear hε hl hε2,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l)+(l - u q)| : by ring_nf
               ... ≤ |u p - l| + |l - u q| : abs_add (u p - l) (l - u q)
               ... = |u p - l| + |u q - l| : by rw abs_sub l (u q)
               ... ≤ ε /2 + ε /2           : add_le_add (hN p hp) (hN q hq)
               ... = ε                     : add_halves ε,
end

/-
DEMOSTRACIÓN 2
-/

example : (∃ l, limite u l) → sucesion_cauchy u :=
begin
  intro h,
  intros ε hε,
  cases h with l hl,
  cases hl (ε /2) (by linarith) with N hN,
  clear hε hl,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l)+(l - u q)| : by ring_nf
               ... ≤ |u p - l| + |l - u q| : abs_add (u p - l) (l - u q)
               ... = |u p - l| + |u q - l| : by rw abs_sub l (u q)
               ... ≤ ε /2 + ε /2           : add_le_add (hN p hp) (hN q hq)
               ... = ε                     : add_halves ε,
end

/-
DEMOSTRACIÓN 3
-/

example : (∃ l, limite u l) → sucesion_cauchy u :=
begin
  intros h ε hε,
  cases h with l hl,
  cases hl (ε /2) (by linarith) with N hN,
  clear hε hl,
  use N,
  intros p q hp hq,
  have cota1 : |u p - l| ≤ ε / 2 := hN p hp, 
  have cota2 : |u q - l| ≤ ε / 2 := hN q hq, 
  clear hN hp hq,
  calc |u p - u q| = |(u p - l)+(l - u q)| : by ring_nf
               ... ≤ |u p - l| + |l - u q| : abs_add (u p - l) (l - u q)
               ... = |u p - l| + |u q - l| : by rw abs_sub l (u q)
               ... ≤ ε                     : by linarith,
end


/-
DEMOSTRACIÓN 4
-/

example : (∃ l, limite u l) → sucesion_cauchy u :=
begin
  intros h ε hε,
  cases h with l hl,
  cases hl (ε /2) (by linarith) with N hN,
  clear hε hl,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l)+(l - u q)| : by ring_nf
               ... ≤ |u p - l| + |l - u q| : abs_add (u p - l) (l - u q)
               ... = |u p - l| + |u q - l| : by rw abs_sub l (u q)
               ... ≤ ε                     : by linarith [hN p (by linarith), hN q (by linarith)],
end


