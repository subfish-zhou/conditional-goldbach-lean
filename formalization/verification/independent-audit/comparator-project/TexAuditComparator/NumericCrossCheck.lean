import ConditionalGoldbach

/-!
Independent finite enumeration check for the Appendix B count.
This is NOT a certificate for the stored character integrals, their RMS error,
or the interval obtained by applying Lemma B.3 to those integral values.
Only kernel-checked propositional computation is used; no native_decide.
-/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace TexAuditAB.Numeric

def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (Nat.sqrt n + 1)).all
    (fun d => decide (d < 2 ∨ ¬d ∣ n))

theorem trialPrime_iff (n : ℕ) : trialPrime n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt]
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hn, hall⟩
    refine ⟨hn, fun d hd hds => ?_⟩
    exact (hall d (by omega)).resolve_left (by omega)
  · rintro ⟨hn, hall⟩
    refine ⟨hn, fun d hd => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · exact Or.inr (hall d (by omega) (by omega))

def computedPairs : Finset ℕ := (Finset.range 30031).filter
  (fun p => p ≤ 30030 - p ∧ trialPrime p = true ∧ trialPrime (30030 - p) = true)

theorem computedPairs_card : computedPairs.card = 905 := by
  decide +kernel

theorem unorderedPrimePairs_eq_905 : ConditionalGoldbach.unorderedPrimePairs = 905 := by
  have heq : ConditionalGoldbach.unorderedPrimePairs = computedPairs.card := by
    unfold ConditionalGoldbach.unorderedPrimePairs computedPairs
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, ConditionalGoldbach.experimentN,
      trialPrime_iff]
    tauto
  exact heq.trans computedPairs_card

#print axioms unorderedPrimePairs_eq_905

end TexAuditAB.Numeric
