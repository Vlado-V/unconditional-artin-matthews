module

public import ArtinMatthews.GiantSignedActualBirthMemoCost
public import ArtinMatthews.GiantSignedMemoTraceComparison


set_option backward.privateInPublic true
@[expose] public section

/-! The actual capped event pays the product of conditional row costs,
including the literal initial Haar-state and tilted active mass. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (η : (i : Fin n) → (a : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i a) s.2.2 → ℂ)
    (v vmin mass : ℝ) (budget : ℕ) (BS W Δ : ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
local notation "Rules" => giantSignedActualBirthMemoRules hPB ν V q ρ θ patterns C κ visitQ ζ K η
  v vmin mass budget BS W Δ σ
local notation "Event" => fun s t => MarkedBirthPermutationEvent
  (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ
local notation "Init" => fun a => GiantSignedUniformBirthConditionalGate σ
  GiantSignedBirthOperation.initial (giantSignedInitialBirthMemo hPB a)

private theorem giantSignedCappedBirthEventPoint_bound
    (hv : 1 ≤ v)
    (hRules : GiantSignedTraceMemoAbsolute (fun s => ENNReal.ofReal (v^(∑ g, s.2.2.1 g))) Rows Rules)
    (cost : ℝ) (hcost0 : 0 ≤ cost) (hcost : giantSignedTraceMemoCost Rows Rules = ENNReal.ofReal cost)
    (s : GiantSignedState PS PB (k+ell)) (hs : s.2.2 = giantSignedEmptyMemory PB) :
    ‖∑' t : GiantSignedCappedTrace H Rows s,
      giantSignedTraceWeight giantSignedBoundary Rows s t.val * (if Event s t then 1 else 0)‖ ≤
        if Init s.2.1 then cost else 0 := by
  let X := GiantSignedState PS PB (k+ell)
  let gauge (x : X) := ENNReal.ofReal (v^(∑ g, x.2.2.1 g))
  let memo : GiantSignedBirthMemo B (k+ell) n H := giantSignedInitialBirthMemo hPB s.2.1
  let good (t : GiantSignedTrace Rows s) :=
    GiantSignedTraceWithin (fun x : X => (∑ g, x.2.2.1 g) ≤ H) Rows s t
  let event (t : GiantSignedCappedTrace H Rows s) := MarkedBirthPermutationEvent
    (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ
  have ha (t : GiantSignedCappedTrace H Rows s) (ht : event t) :
      GiantSignedUniformBirthConditionalGate σ .initial memo ∧
        GiantSignedTraceMemoAccept Rows Rules memo s t.val :=
    giantSignedActualBirthMemoRules_accept hPB ν V q ρ θ patterns C κ visitQ ζ K η
      v vmin mass budget BS W Δ σ s t ht
  change ‖∑' t : GiantSignedCappedTrace H Rows s,
    giantSignedTraceWeight giantSignedBoundary Rows s t.val * (if event t then 1 else 0)‖ ≤
      if GiantSignedUniformBirthConditionalGate σ .initial memo then cost else 0
  by_cases hi : GiantSignedUniformBirthConditionalGate σ .initial memo
  · rw [ite_eq_left hi]
    have hterm (x : X) : ENNReal.ofReal ‖giantSignedBoundary x‖ ≤ gauge x := by
      apply ENNReal.ofReal_le_ofReal
      apply le_trans _ (one_le_pow₀ hv)
      unfold giantSignedBoundary
      split_ifs <;> simp
    have hfinite : Finite {t : GiantSignedTrace Rows s // good t} :=
      giantSignedChronologicalTraceWithin_finite ν V q ρ θ H n patterns C κ visitQ ζ K η s
    have h := giantSignedMemoTraceComparison giantSignedBoundary Rows Rules memo s good hfinite
      event (fun t ht => (ha t ht).2)
    have hg : gauge s = 1 := by
      unfold gauge
      rw [hs]
      simp only [giantSignedEmptyMemory, Finset.sum_const_zero, pow_zero, ENNReal.ofReal_one]
    have hm := giantSignedTraceMemoMass_le giantSignedBoundary gauge hterm Rows Rules hRules memo s
    rw [hcost, hg, mul_one] at hm
    exact (ENNReal.ofReal_le_ofReal_iff hcost0).mp (h.trans hm)
  · have hn (t : GiantSignedCappedTrace H Rows s) : ¬ event t := fun he => hi (ha t he).1
    simp only [hi, hn, ite_false, mul_zero, tsum_zero, norm_zero, le_refl]

private theorem norm_weighted_sum_with_gate {Y L : Type*} [Fintype Y] [Fintype L]
    (F : Y → L → ℂ) (μ : L → ℝ) (hμ : ∀ a, 0 ≤ μ a) (gate : L → Prop)
    (cost : ℝ) (hpoint : ∀ y a, ‖F y a‖ ≤ if gate a then cost else 0) :
    ‖∑ y, ∑ a, (μ a : ℂ) * F y a‖ ≤
      (∑ _ : Y, ∑ a, if gate a then μ a else 0) * cost := by
  calc
    _ ≤ ∑ y : Y, ∑ a : L, μ a * (if gate a then cost else 0) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ a)]
      exact mul_le_mul_of_nonneg_left (hpoint y a) (hμ a)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hi : gate a <;> simp only [hi, ite_true, ite_false, mul_zero, zero_mul]

private theorem capped_boundary_norm_with_gate
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (rs : List (GiantSignedTraceRow (GiantSignedState PS PB (k+ell))))
    (φ : (s : GiantSignedState PS PB (k+ell)) → GiantSignedCappedTrace H rs s → ℂ)
    (gate : MarkedPhysicalMarking PB (k+ell) → Prop) (cost : ℝ)
    (hμ : ∀ a : MarkedPhysicalMarking PB (k+ell),
      0 ≤ giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a)
    (hf : ∀ y a,
      let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
      ‖∑' t : GiantSignedCappedTrace H rs s,
        giantSignedTraceWeight giantSignedBoundary rs s t.val * φ s t‖ ≤
        if gate a then cost else 0) :
    ‖giantSignedCappedTraceBoundaryPairing H ν rs φ‖ ≤
      (∑ _ : GiantTwoSidedResidueState PS (k+ell), ∑ a : MarkedPhysicalMarking PB (k+ell),
        if gate a then giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a else 0) * cost := by
  let F (y : GiantTwoSidedResidueState PS (k+ell)) (a : MarkedPhysicalMarking PB (k+ell)) :=
    let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
    ∑' t : GiantSignedCappedTrace H rs s, giantSignedTraceWeight giantSignedBoundary rs s t.val * φ s t
  let μ (a : MarkedPhysicalMarking PB (k+ell)) :=
    giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a
  have he : giantSignedCappedTraceBoundaryPairing H ν rs φ = ∑ y, ∑ a, (μ a : ℂ) * F y a := by
    unfold giantSignedCappedTraceBoundaryPairing
    apply Finset.sum_congr rfl
    intro y _
    refine Finset.sum_congr (by ext a; simp only [Finset.mem_univ]) ?_
    intro a _
    rfl
  rw [he]
  exact norm_weighted_sum_with_gate F μ hμ gate cost hf

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

include hPS hdis hVS hν in
theorem giantSignedCappedBirthEventBoundary_norm_le_of_rules
    (hv : 1 ≤ v) (hMass : 1 ≤ mass) (hΔ : 0 ≤ Δ)
    (hatom : ∀ g p, ν g p ≤ Δ) (hνMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (hRules : GiantSignedTraceMemoAbsolute (fun s => ENNReal.ofReal (v^(∑ g, s.2.2.1 g))) Rows Rules)
    (cost : ℝ) (hcost0 : 0 ≤ cost) (hcost : giantSignedTraceMemoCost Rows Rules = ENNReal.ofReal cost) :
    ‖giantSignedCappedBirthEventBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ‖ ≤
      (Δ^(giantSignedUniformBirthStageNonpivots σ .initial).card * mass^(Fintype.card B*(k+ell))) * cost := by
  let μ (a : MarkedPhysicalMarking PB (k+ell)) :=
    giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a
  have hμ (a : MarkedPhysicalMarking PB (k+ell)) : 0 ≤ μ a := by
    unfold μ giantTwoSidedResidueHaarStateMass markedPhysicalMass giantSignedActiveMass
    exact mul_nonneg
      (div_nonneg (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _))
        (Nat.cast_nonneg _))
      (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g (a g i))))
  have hInit : (∑ _ : GiantTwoSidedResidueState PS (k+ell),
      ∑ a : MarkedPhysicalMarking PB (k+ell), if Init a then μ a else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ .initial).card * mass^(Fintype.card B*(k+ell)) := by
    have h := giantSignedInitialBirthBoundary_mass_le hPB ν hν hΔ hMass hatom hνMass σ PS hPS hdis hVS
    refine (le_of_eq (Finset.sum_congr ?_ ?_)).trans h
    · ext y
      simp only [Finset.mem_univ]
    · intro y _
      refine Finset.sum_congr (by ext a; simp only [Finset.mem_univ]) ?_
      intro a _
      rfl
  unfold giantSignedCappedBirthEventBoundary
  refine (capped_boundary_norm_with_gate (H := H) ν Rows _ Init cost hμ ?_).trans
    (mul_le_mul_of_nonneg_right hInit hcost0)
  intro y a
  let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
  exact giantSignedCappedBirthEventPoint_bound hPB ν V q ρ θ patterns C κ visitQ ζ K η
    v vmin mass budget BS W Δ σ hv hRules cost hcost0 hcost s rfl

end
end ArtinMatthews
