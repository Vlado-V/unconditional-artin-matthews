module

public import ArtinMatthews.GiantCandidatePhysicalDyadicAssembly
public import ArtinMatthews.GiantCandidateRetainedSourcePairingActual
public import ArtinMatthews.GiantCandidatePhysicalTailUniform
public import ArtinMatthews.GiantCandidatePhysicalMellinWindowNormalized


set_option backward.privateInPublic true
@[expose] public section

/-! The selected physical residual is small on the common unmasked box.
The family is chosen after the saving, and the Mellin tail order is chosen
after the absolute mass exponent of that family. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidateRetainedResidualCutoff_eventually
    {Jtest : Type*} [Fintype Jtest] (e : Jtest → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) {mχ : ℕ} (χ : DirichletCharacter ℂ mχ)
    (threshold E γ : ℝ) (hthreshold : 0 < threshold) (hγ : 0 < γ) (j : ℕ) (hj : 0 < j)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support Ψ ⊆ Set.Icc a b) (hΨ : ContDiff ℝ ∞ Ψ) :
    ∃ Eid : ℝ, 0 < Eid ∧ ∃ m J₀ : ℕ, 1 ≤ m ∧ idealSourceDimensionThreshold m 1 ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J → ∀ᶠ x : ℝ in atTop,
        let L := Real.log x
        ∀ groups ∈ giantCandidateRetainedOutcomes x threshold,
        let B := GiantCandidatePerformedBig groups
        let PB := giantCandidatePerformedBigBand groups
        let P := fun g : ↥groups => giantCandidateGroup x g.val
        ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = univ ∧
          let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
          let vmin := Real.log 2/2
          let C₀ := giantCandidateGroupLogRate
          let d := (45/100 : ℝ)
          let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
          let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d 2 m)
          let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d 2 m)
          let W := 1 + ((Q : ℝ)^2 / ξ)^2
          (∀ p ∈ family, ∀ g, (idealResidualCopied p g).card ≤ m) ∧
          (family.card : ℝ)*W ≤ L^(idealSourceCostExponent (Eid+1) C₀ vmin d 2 m) ∧
          let copied (p : IdealResidualPattern B J) := giantCandidatePerformedPattern groups (idealResidualCopied p)
          let K (p : IdealResidualPattern B J) : GiantTwoSidedPatternCoefficient P (copied p) 1 :=
            giantCandidatePerformedCoefficient groups (idealResidualCoefficient PB Q h ξ p)
          let Z := Ioc 0 ⌊x^2⌋₊
          let F (r : ℕ) := conj (giantCandidateFirstEndpoint e ε x r)
          let G (r : ℕ) := χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
            (univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r
          let damp (r : ℕ) := (giantTwoSidedEndpointDamping P (J+1) q r : ℂ)
          ∀ u v : ℕ → ℂ, (∀ r, ‖u r‖ ≤ 1) → (∀ r, ‖v r‖ ≤ 1) →
            ‖giantTwoSidedPhysicalCutoffPairing (Z := Z) family copied 1 q 0 K Ψ x
              (fun r => damp r*(u r*F r)) (fun t => damp t.val.1.val*(v t.val.1.val*G t.val.1.val))‖ ≤
                L^(-E) := by
  let τ : ℝ := 1/2
  let save : ℝ := E+4
  have hτ : 0 < τ := by norm_num [τ]
  have hzero : ∀ t < a, Ψ t = 0 := by
    intro t ht
    by_contra h
    exact (not_le_of_gt ht) (hsupp h).1
  obtain ⟨Eid,hEid,m,J₀,hm,hJ₀,hselect⟩ := giantCandidateRetainedSourcePairing_eventually
    e he hε hεq χ threshold 2 0 save γ τ hthreshold 1 j (by decide) hj hq hq1 (by norm_num) hγ hτ
  let cost := idealSourceCostExponent (Eid+1) giantCandidateGroupLogRate (Real.log 2/2) (45/100) 2 m
  obtain ⟨A,_,htail⟩ := giantCandidatePhysicalFamily_absolute_tail_uniform_eventually.{0}
    e he hε hεq χ hγ hτ hq hq1 j 1 m hj cost
  obtain ⟨_,_,hMellin⟩ := giantTwoSidedPhysicalCutoffPairing_logSaving.{0,0} Ψ ha hsupp hΨ
    (cost+A+((j*j : ℕ) : ℝ)+2) save 1 (E+2) (by norm_num) (by dsimp [save]; linarith)
  refine ⟨Eid,hEid,m,J₀,hm,hJ₀,?_⟩
  intro J hJ
  filter_upwards [hselect J hJ, htail, hMellin,
    giantCandidatePhysicalMellinWindow_normalized_eventually.{0,0} e ε γ χ j save 1,
    giantCandidatePhysicalCutoff_log_saving_of_local.{0} J ha hτ (le_refl (1/2)) Ψ hzero E,
    eventually_gt_atTop (1 : ℝ), giantCandidateFullPrimes_prime_upper_eventually]
    with x hselect htail hMellin hwindow hdyad hx hprime
  intro L groups hgroups B PB P
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hpair⟩ := hselect groups hgroups
  refine ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,?_⟩
  intro copied K Z F G damp u v hu hv
  let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
  let vmin := Real.log 2/2
  let C₀ := giantCandidateGroupLogRate
  let d : ℝ := 45/100
  let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
  let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d 2 m)
  let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d 2 m)
  let W := 1 + ((Q : ℝ)^2 / ξ)^2
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL0 : 0 < L := Real.log_pos hx
  have hP (i : ↥groups) (p : ℕ) (hp : p ∈ P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  have hcap' (p : IdealResidualPattern B J) (hp : p ∈ family) (g : ↥groups) :
      (copied p g).card ≤ m := by
    rcases g with ⟨g | g, hg⟩
    · change (∅ : Finset (Fin J)).card ≤ m
      simp
    · exact hcap p hp ⟨g,hg⟩
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL0 _
  have hW : 0 ≤ W := zero_le_one.trans (le_add_of_nonneg_right (sq_nonneg _))
  have hK (p : IdealResidualPattern B J) (_ : p ∈ family) :
      0 ≤ W ∧ ∀ b c aux, ‖K p b c aux‖ ≤ W :=
    ⟨hW, fun b c aux => idealResidualCoefficient_norm PB Q h hξ p _ _ _⟩
  have hcost' : (∑ _p ∈ family, W) ≤ L^cost := by
    rw [sum_const,nsmul_eq_mul]
    exact hcost
  apply hdyad groups (IdealResidualPattern B J) family copied 1 K q 0
    (fun r => damp r*(u r*F r)) (fun r => damp r*(v r*G r))
  intro X hX hXhi
  let roots := giantTwoSidedRootInterval X
  let slice := giantTwoSidedRootSlice X
  let State := GiantTwoSidedEndpointState P (J+1) slice
  let uZ (r : ℕ) := if r ∈ Z then u r else 0
  let vZ (r : ℕ) := if r ∈ Z then v r else 0
  let left (r : ℕ) := damp r*(if r ∈ roots then uZ r*F r else 0)
  let right (t : State) := damp t.val.1.val*(vZ t.val.1.val*G t.val.1.val)
  have huZ : ∀ r ∈ roots, ‖uZ r‖ ≤ 1 := by
    intro r _
    by_cases hr : r ∈ Z <;> simp [uZ,hr,hu r]
  have hvZ : ∀ r ∈ slice, ‖vZ r‖ ≤ 1 := by
    intro r _
    by_cases hr : r ∈ Z <;> simp [vZ,hr,hv r]
  have hleft : (fun r => if r ∈ Z then
      giantPhysicalDyadicLeft X (fun n => damp n*(u n*F n)) r else 0) = left := by
    funext r
    by_cases hz : r ∈ Z <;> by_cases hr : r ∈ roots <;>
      simp [left,uZ,roots,giantPhysicalDyadicLeft,hz,hr]
  have hright : (fun t : State => if t.val.1.val ∈ Z then
      damp t.val.1.val*(v t.val.1.val*G t.val.1.val) else 0) = right := by
    funext t
    by_cases ht : t.val.1.val ∈ Z <;> simp [right,vZ,ht]
  have hX0 : 0 < X := (Real.rpow_pos_of_pos hx0 τ).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_rpow hx.le hτ.le).trans hX
  have hmass := htail (IdealResidualPattern B J) groups J family copied hcap' 1 0 K
    (fun _ => W) hK hcost' X hX1 hXhi uZ vZ huZ hvZ
  have hw := hwindow (P := P) (X := X) family copied 1 q K hX0 (by
    intro ζ hζ u' v' hu' hv'
    exact hpair 1 (by decide) (by norm_num) ζ (by simpa only [show (1 : ℝ)+1 = 2 by norm_num] using hζ)
      X hX hXhi u' v' hu' hv') uZ vZ huZ hvZ
  rw [hleft,hright]
  exact hMellin hP (fun n hn => (mem_Ioc.mp hn).1) family copied 1 q 0 K left right hmass hw

end
end ArtinMatthews
