import Mathlib
lemma upup (d s t: ℕ) (a b : ℤ) (ha: a ≥ 0) (hb: b ≥ 0) (h: s * a + d = t * b) : ∃ m n : ℕ, s * m + d =  t * n := by
  refine' ⟨(Int.natAbs a), (Int.natAbs b), _⟩
  rw [← (Int.natAbs_of_nonneg ha), ← (Int.natAbs_of_nonneg hb)] at h
  exact Int.ofNat_inj.1 h
#check Int.natAbs
#check Int.ofNat_inj
theorem Nat.bezout {s t : ℕ } (h₂: 0 < t): ∃ m : ℕ ,∃ n : ℕ , s * m + Nat.gcd s t = t * n:= by
  by_cases h₁: s ≤ 0
  · have eq_zero: s=0 :=by exact eq_zero_of_le_zero h₁
    rw[eq_zero]
    use 0;use 1
    ring_nf
    exact rfl
  · push_neg at h₁
    let x := Nat.gcdA s t
    let y := Nat.gcdB s t
    have L1 : s * (t * (|x| + |y|) - x) +  s.gcd t = t * (s *(|x| + |y|) + y) := by
      rw [Nat.gcd_eq_gcd_ab]
      ring
    have L2 : 0 ≤ (t * (|x| + |y|) - x):= by
      apply sub_nonneg.mpr
      have ge_one: 1≤ (t:ℤ ):=by exact Int.toNat_le.mp h₂
      nth_rw 1[←one_mul x]
      have ge_x : x≤ |x| :=by exact le_abs_self x
      have ge_zero : 0≤ |y|:=by exact abs_nonneg y
      have add_ge : x≤ |x|+|y| :=by exact le_add_of_le_of_nonneg ge_x ge_zero
      refine mul_le_mul_of_le_of_le ge_one add_ge ?a0 ?d0
      · exact Int.one_nonneg
      · refine Int.add_nonneg ?d0.ha ge_zero
        exact abs_nonneg x
    have L3 : 0 ≤ (s * (|x| + |y|) + y) := by
      have mul_ge : |x|+|y|≤ s*(|x|+|y|) :=by
        nth_rw 1[←one_mul (|x|+|y|)]
        refine Int.mul_le_mul_of_nonneg_right ?h₁ ?h₂
        exact Int.toNat_le.mp h₁
        refine Int.add_nonneg ?h₂.ha ?h₂.hb
        ·exact abs_nonneg x
        ·exact abs_nonneg y
      have pos : 0≤|x|+|y|+y :=by
        by_cases pos : 0≤y
        ·refine Int.add_nonneg ?_ pos
         ·refine Int.add_nonneg ?_ ?_
          exact abs_nonneg x
          exact abs_nonneg y
        · rw[add_assoc]
          refine Int.add_nonneg ?_ ?_
          · exact abs_nonneg x
          · refine (Lean.Omega.Int.add_nonnneg_iff_neg_le |y| y).mpr ?_
            have rpl: |y|=|-y| :=by exact Eq.symm (abs_neg y)
            rw[rpl]
            exact le_abs_self (-y)
      exact le_add_of_le_add_right pos mul_ge
    exact upup (Nat.gcd s t) s t (t * (|x| + |y|) - x) (s * (|x| + |y|) + y) L2 L3 L1

-- Finset.sum ∧ Finset.prod
section

variable {α : Type u₃} {β : Type u₄} [AddCommMonoid β] [CommMonoid β] (s' : Finset α) (f' : α → β)

--example
variable (s : Finset ℕ) (f : ℕ → ℕ)
open BigOperators
open Finset
example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring

-- practice
variable {X : Type*} [MetricSpace X]
open Set Filter
open Topology Filter
example (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := sorry

example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    use Nat.clog 2 ⌈2 / ε + 1⌉₊
    rw [← lt_div_iff]
    · rw [div_lt_div_iff]
      · simp
        rw [mul_comm]
        apply (div_lt_iff ε_pos).mp
        apply lt_of_lt_of_le (lt_add_one (2 / ε))
        apply le_trans (Nat.le_ceil (2 / ε + 1))
        norm_cast
        apply Nat.le_pow_clog
        norm_num
      · simp
      · norm_num
    · norm_num
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by
      rw [add_zero]
      rw [dist_comm]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := dist_le_range_sum_dist (fun i ↦ u (N + i)) k
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := by
      apply sum_le_sum
      intro i _
      exact hu (N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by
      rw [← one_div_pow]
      simp_rw [pow_add]
      rw [← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 := by
      apply mul_le_mul_of_nonneg_left
      exact sum_geometric_two_le k
      norm_num
    _ < ε := hN

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := sorry

end

-- tsum ∧ tprod
section
end
