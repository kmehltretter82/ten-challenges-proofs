import Defs_and_Lems.MatroidRepresentability
set_option linter.all false

theorem Submission.challenge_2_proof : ∀ (p m : ℕ) [Fact p.Prime], 0 < m → p ^ m ≤ 1 → ExcludedMinorsAtMost p m 0 := by
  intro p m hp hm hpow
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow2 : 2 ≤ p ^ m := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
  omega