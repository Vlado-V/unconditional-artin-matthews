module

public import ArtinMatthews.GiantSignedEdgePairingReal
public import ArtinMatthews.GiantSignedEdgeReverseBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The original factorial pairing reverses with its literal promotion charge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

theorem giantSignedEdgeCoupledENNPairing_reverse_charge
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (hs : ∀ S T source target out old σ,
      F S T source target (giantSignedMemoryPermute old σ) out = F S T source target old out)
    (ht : ∀ S T source target old out σ,
      F S T source target old (giantSignedMemoryPermute out σ) = F S T source target old out) :
    giantSignedEdgeCoupledENNPairing ν V ρ d
        (fun S T source target old out => ENNReal.ofReal (F S T source target old out)) =
      ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ENNReal.ofReal (∏ j, (V j) ^ (S j).card / (V j) ^ (T j).card) *
          ∑' n : J → ℕ, giantSignedEdgeENNStorePairing ν V ρ (-d) n T S
            (fun U W source target old out => ENNReal.ofReal (F W U target source out old)) := by
  rw [giantSignedEdgeCoupledENNPairing_blocks]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  rw [giantSignedEdgeENNStorePairing_ofReal ν hν V (fun j => (hV j).le) hρ d F hF,
    giantSignedEdgeENNStorePairing_ofReal ν hν V (fun j => (hV j).le) hρ (-d)
      (fun U W source target old out => F W U target source out old)
      (fun U W source target old out => hF W U target source out old),
    giantSignedEdgeRealStorePairing_reverse ν V (fun j => (hV j).ne') ρ d n S T
      (F S T) (hs S T) (ht S T)]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ =>
    div_nonneg (pow_nonneg (hV j).le _) (pow_nonneg (hV j).le _))]

theorem giantSignedEdgeCoupledENNPairing_reverse_le
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (tmax : ℕ) (htmax : ∀ j, t j ≤ tmax)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (hs : ∀ S T source target out old σ,
      F S T source target (giantSignedMemoryPermute old σ) out = F S T source target old out)
    (ht : ∀ S T source target old out σ,
      F S T source target old (giantSignedMemoryPermute out σ) = F S T source target old out) :
    giantSignedEdgeCoupledENNPairing ν V ρ d
        (fun S T source target old out => ENNReal.ofReal (F S T source target old out)) ≤
      ENNReal.ofReal ((giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J) *
        giantSignedEdgeCoupledENNPairing ν V ρ (-d)
          (fun S T source target old out => ENNReal.ofReal (F T S target source out old)) := by
  let R := (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J
  let F' : GiantSignedEdgeCoupledTest P t ℝ≥0∞ :=
    fun S T source target old out => ENNReal.ofReal (F T S target source out old)
  let H (S T : (j : J) → Finset (Fin (t j))) :=
    ∑' n : J → ℕ, giantSignedEdgeENNStorePairing ν V ρ (-d) n T S F'
  have hcard (S : (j : J) → Finset (Fin (t j))) (j : J) : (S j).card ≤ tmax := by
    have hj := Finset.card_le_univ (S j)
    rw [Fintype.card_fin] at hj
    exact hj.trans (htmax j)
  rw [giantSignedEdgeCoupledENNPairing_reverse_charge ν hν V
    (fun j => hvmin.trans_le (hVmin j)) hρ d F hF hs ht]
  change (∑ S, ∑ T, ENNReal.ofReal (∏ j, (V j) ^ (S j).card / (V j) ^ (T j).card) * H S T) ≤
    ENNReal.ofReal R * giantSignedEdgeCoupledENNPairing ν V ρ (-d) F'
  calc
    _ ≤ ∑ S, ∑ T, ENNReal.ofReal R * H S T := by
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (giantSignedEdgeReverseFactor_bound V hvmin hVmin hVmax
          (fun j => (T j).card) (fun j => (S j).card) tmax (hcard T) (hcard S))) (H S T)
    _ = ENNReal.ofReal R * ∑ S, ∑ T, H S T := by simp only [Finset.mul_sum]
    _ = ENNReal.ofReal R * (∑ T, ∑ S, H S T) :=
      congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal R * x) Finset.sum_comm
    _ = _ := by rw [giantSignedEdgeCoupledENNPairing_blocks]

end
end ArtinMatthews
