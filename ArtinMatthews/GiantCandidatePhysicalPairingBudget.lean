module

public import ArtinMatthews.GiantTwoSidedPhysicalLocalizedPairing
public import ArtinMatthews.GiantCandidatePhysicalCellWidth
public import ArtinMatthews.GiantTwoSidedPhysicalPairingScalars


set_option backward.privateInPublic true
@[expose] public section

/-! The source even-moment estimate controls the physical pairing on the
literal dyad. The right vector may depend on every state coordinate. -/
namespace ArtinMatthews
open Filter Matrix
open scoped BigOperators ComplexOrder
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

theorem giantCandidatePhysicalPairing_eventually_of_moment (k ell : ℕ)
    (Cstep Ctest E q : ℝ) (hCtest : 0 ≤ Ctest) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      let P := fun j : ↥groups => giantCandidateGroup x j.val
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      ∀ (I : Type u) (patterns : Finset I) (C : I → ↥groups → Finset (Fin k))
        (step : ℤ), (step.natAbs : ℝ) ≤ L^Cstep →
      ∀ (ζ : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (X : ℝ), x^γ ≤ X →
      let roots := giantTwoSidedRootInterval X
      let Z := giantTwoSidedRootSlice X
      let T := giantTwoSidedExpandedPhysicalMoment (fun _ : Fin n => patterns) (fun _ => C)
        (fun i => if i.val%2 = 0 then step else -step) q (fun i => if i.val%2 = 0 then ζ else -ζ)
        (fun i p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) roots Z
      ‖T‖ / ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) ≤ (L^(-E))^n →
      let State := GiantTwoSidedEndpointState P (k+ell) Z
      let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
      ∀ (f : ℕ → ℂ) (g : State → ℂ),
        (∀ r ∉ roots, f r = 0) → (∀ r ∈ roots, ‖f r‖ ≤ Real.exp (Real.sqrt L)) →
        (∑ s : State, σ*‖f s.val.1.val‖^2) ≤ X*L^(2*Ctest) →
        (∑ s : State, σ*‖g s‖^2) ≤ X*L^(2*Ctest) →
        ‖giantTwoSidedPhysicalWeightedPairing (giantTwoSidedPhysicalFamilyMatrix patterns C step q ζ K)
          (fun s => f s.val.1.val) g‖ ≤ 8*X*L^(-E+2*Ctest) := by
  filter_upwards [giantCandidatePhysicalCellWidth_eventually k Cstep,
    giantCandidatePhysicalCellWidth_root_eventually k Cstep, giantCandidateRootInterval_budget hγ,
    giantCandidateFullPrimes_prime_upper_eventually, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hwidth hcell hinterval hprime hx hL
  intro groups P L n I patterns C step hstep ζ K X hX roots Z T hT State σ f g hf hsup hEf hEg
  let H := giantCandidatePhysicalCellWidth k Cstep x
  let U := Real.exp (Real.sqrt L)
  let R := ⌈L^(13/25 : ℝ)⌉₊
  let r := R-1
  let len := ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hX1 : 1 ≤ X := (Real.one_le_rpow hx.le hγ.le).trans hX
  have hlen : 0 < len := (Real.exp_pos _).trans_le (hinterval X hX).2
  have hR : 1 ≤ R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL0 _)
  have hr : r+1 = R := Nat.sub_add_cancel hR
  have hn : 2*(r+1) = n := by rw [hr]; rfl
  have hnr : (n : ℝ) = 2*((r+1:ℕ):ℝ) := by rw [← hn, Nat.cast_mul, Nat.cast_ofNat]
  have hP (j : ↥groups) (p : ℕ) (hp : p ∈ P j) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
  have hD (p : I) (_ : p ∈ patterns) (a : MarkedPhysicalMarking P (k+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (C p)) : step.natAbs*giantTwoSidedPatternDilation (C p) a aux ≤ H :=
    hwidth.2 groups ell (C p) a aux step hstep
  have hZ : roots ⊆ Z := by
    intro a ha
    obtain ⟨ha1,ha2⟩ := giantTwoSidedRootInterval_bounds ha
    exact Finset.mem_Ioc.mpr ⟨Nat.cast_pos.mp ((zero_lt_one.trans_le hX1).trans_le ha1),
      Nat.cast_le.mp ((show (a:ℝ) ≤ 3*X by linarith).trans (Nat.le_ceil _))⟩
  have hp := giantTwoSidedPhysicalPairing_localized_root hP hwidth.1 patterns C step q ζ K hD
    roots Z hZ f g hf U hsup r
  have hT0 : 0 ≤ T.re := by
    have ht := giantTwoSidedPhysicalPositionTrace_eq_expanded hP patterns C step q ζ K roots Z R
    change (∑ a ∈ roots, markedQuadraticForm _ _) = T.re at ht
    rw [← ht]
    apply Finset.sum_nonneg
    intro a _
    let A := giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C step q ζ K
    let v := markedPositionVector (fun s : State => s.val.1.val) σ a
    exact ((Matrix.posSemidef_self_mul_conjTranspose A).pow R).re_dotProduct_nonneg v
  have hT' : T.re ≤ 2*X*(L^(-E))^(2*(r+1)) := by
    have hnorm : ‖T‖ ≤ len*(L^(-E))^n := by
      rw [mul_comm]
      exact (div_le_iff₀ hlen).mp hT
    rw [hn]
    exact (Complex.re_le_norm _).trans (hnorm.trans (mul_le_mul_of_nonneg_right
      (giantTwoSidedRootInterval_length_le hX1) (pow_nonneg (Real.rpow_nonneg hL0.le _) _)))
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ =>
    Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have hnon (w : State → ℂ) : 0 ≤ ∑ s : State, σ*‖w s‖^2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg hσ (sq_nonneg _))
  have hcell' : ((H:ℝ)*U^2)^((2*((r+1:ℕ):ℝ))⁻¹) ≤ 2 := by
    rw [← hnr]
    exact hcell
  have hpair := giantTwoSidedPhysicalPairing_scalar r hL hX1 hCtest (hnon (fun s => f s.val.1.val))
    (hnon g) hT0 (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg H) (sq_nonneg U)) _)
    hEf hEg hT' hcell'
  apply le_trans _ hpair
  let alt (length : ℕ) := giantTwoSidedExpandedPhysicalMoment (fun _ : Fin length => patterns) (fun _ => C)
    (fun i => if i.val%2 = 0 then step else -step) q (fun i => if i.val%2 = 0 then ζ else -ζ)
    (fun i p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) roots Z
  have hAlt : alt (2*(r+1)) = T := congrArg alt hn
  rw [← hAlt]
  exact hp

end
end ArtinMatthews
