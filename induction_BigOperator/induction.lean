import Mathlib


def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · exact Nat.zero_lt_succ 0
  rw [fac]
  exact Nat.succ_mul_pos n ih


example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction' b with d hd generalizing c
  · rw [mul_zero] at h
    have := mul_eq_zero.mp h.symm
    tauto
  -- · induction' c with e _
  --   · rw [mul_zero] at h
  --     have := mul_eq_zero.mp h
  --     tauto
  --   · repeat rw [mul_add] at h
  --     rw [mul_one] at h
  --     have g := add_right_cancel h
  --     have := hd e g
  --     rw [this]
  · cases' c with e
    · rw [mul_zero] at h
      have := mul_eq_zero.mp h
      tauto
    · repeat rw [mul_add] at h
      rw [mul_one] at h
      have g := add_right_cancel h
      have := hd e g
      rw [this]


variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

example {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  -- induction s using Finset.induction with
  -- | empty =>
  --     simp
  -- | @insert i s _ hs =>
  --     rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
  --     set K := ⨅ j ∈ s, J j
  --     calc
  --       1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
  --       _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
  --       _ = (1 + K) * I + K * J i  := by ring
  --       _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf
  induction' s using Finset.induction with i s _ hs
  · simp
  · rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
    set K := ⨅ j ∈ s, J j
    calc
      1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
      _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
      _ = (1 + K) * I + K * J i  := by ring
      _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf
