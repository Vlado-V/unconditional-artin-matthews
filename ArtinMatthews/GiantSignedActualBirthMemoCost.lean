module

public import ArtinMatthews.GiantSignedActualBirthMemo


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual visit and full pattern edge has its conditional row
bound on one common degree gauge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
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
local notation "VisitRules" => giantSignedVisitMemoRule (PS := PS) hPB ν V ρ visitQ v mass Δ σ
local notation "EdgeRules" => fun i => giantSignedEdgeMemoRule hPB ν V (patterns i) (C i) (κ i) q ρ θ
  (ζ i) (K i) (η i) v vmin mass budget BS W Δ σ i

def giantSignedActualBirthVisitCost (i : Fin (n+1)) : ℝ :=
  Δ^(giantSignedUniformBirthStageNonpivots σ (.visit i)).card *
    ∏ g, Real.exp (|-(1-visitQ i)*V g/ρ| * mass * v)

def giantSignedActualBirthEdgeCost (i : Fin n) : ℝ :=
  (patterns i).card * W * Δ^(giantSignedUniformBirthStageNonpivots σ (.edge i)).card *
    (giantSignedEdgeUniformConstant ρ v vmin⁻¹ mass (ell+budget))^Fintype.card B *
    BS^Fintype.card S

theorem giantSignedActualBirthMemoRules_cost
    (hv : 0 ≤ v) (hρ : ρ < 1) (hBS : 0 ≤ BS) (hW : 0 ≤ W) (hΔ : 0 ≤ Δ) :
    giantSignedTraceMemoCost Rows Rules =
      ENNReal.ofReal ((∏ i, giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i) *
        ∏ i, giantSignedActualBirthEdgeCost (S := S) ρ patterns v vmin mass budget BS W Δ σ i) := by
  have hV (i : Fin (n+1)) : (VisitRules i).cost =
      ENNReal.ofReal (giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i) := by
    simp only [giantSignedVisitMemoRule, giantSignedGhostMemoRule, giantSignedActualBirthVisitCost,
      Complex.norm_real, Real.norm_eq_abs]
  have hE (i : Fin n) : (EdgeRules i).cost =
      ENNReal.ofReal (giantSignedActualBirthEdgeCost (S := S) ρ patterns v vmin mass budget BS W Δ σ i) := rfl
  have hV0 (i : Fin (n+1)) : 0 ≤ giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i := by
    unfold giantSignedActualBirthVisitCost
    positivity
  have hE0 (i : Fin n) : 0 ≤ giantSignedActualBirthEdgeCost (S := S) ρ patterns v vmin mass budget BS W Δ σ i := by
    have hC := giantSignedEdgeUniformConstant_nonneg (rateMax := vmin⁻¹) (massMax := mass)
      (tmax := ell+budget) hρ hv
    unfold giantSignedActualBirthEdgeCost
    positivity
  change giantSignedTraceMemoCost Rows
    (giantSignedChronologicalMemoRules ν V q ρ θ n patterns C κ visitQ ζ K η VisitRules EdgeRules) = _
  rw [giantSignedChronologicalMemoRules_cost, ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => hV0 i))]
  simp only [hV, hE, ENNReal.ofReal_prod_of_nonneg (fun i _ => hV0 i),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hE0 i)]

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedActualBirthMemoRules_absolute
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (hν : ∀ g p, 0 ≤ ν g p) (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hmass : 1 ≤ mass) (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hW : 0 ≤ W) (hΔ : 0 ≤ Δ)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (hC : ∀ i a, a ∈ patterns i → ∀ g, (C i a g).card ≤ budget)
    (hK : ∀ i a, a ∈ patterns i → ∀ x y aux, ‖K i a x y aux‖ ≤ W)
    (hη : ∀ i a, a ∈ patterns i → ∀ s r, ‖η i a s r‖ ≤ 1)
    (hrow : ∀ i, |visitQ i/ρ^2| + |-(1-visitQ i)/ρ| / v ≤ 1) :
    GiantSignedTraceMemoAbsolute (fun s => ENNReal.ofReal (v^(∑ g, s.2.2.1 g))) Rows Rules := by
  apply giantSignedChronologicalMemoRules_absolute ν V q ρ θ n patterns C κ visitQ ζ K η VisitRules EdgeRules
  · intro i
    refine ⟨fun old s => ?_,trivial⟩
    exact giantSignedGhostMemoRule_mass_le hPB ν hν
      (fun _ => ((visitQ i/ρ^2 : ℝ) : ℂ)) (fun g => ((-(1-visitQ i)*V g/ρ : ℝ) : ℂ))
      (fun _ => ((-(1-visitQ i)/ρ : ℝ) : ℂ)) (zero_lt_one.trans_le hv)
      hmass hΔ hatom hMass
      (fun _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hrow i) σ i old s
  · intro i
    exact ⟨fun old s => giantSignedEdgeMemoRule_mass_le hPS hPB hdis hVS hVB ν hν V
      hvmin hV hmass hq hq1 hBS hbudget hρ hρ1 hv hW hΔ budget (patterns i) (C i) (hC i)
      (κ i) θ (ζ i) (K i) (hK i) (η i) (hη i) hatom hMass σ i old s,trivial⟩

end
end ArtinMatthews
