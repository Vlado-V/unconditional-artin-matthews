module

public import ArtinMatthews.MarkedMajorScalarMellin
public import ArtinMatthews.MarkedMajorScalarArcAssembly
public import ArtinMatthews.MarkedMajorTypeIIBands


set_option backward.privateInPublic true
@[expose] public section

/-! Full scalar major saving on the actual selected prime bands, under
the original boundedness, rough support, and long character tests. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology
noncomputable section

theorem markedMajorScalar_actual_log_saving
    {I : Type} [Fintype I] [DecidableEq I] (i₀ : I)
    (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (δ Kx a Cα Cβ D : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hD : 0 ≤ D) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y H U : ℝ) (S : Finset ℕ) (l r : ℕ) (α β : ℕ → ℂ),
        0 < Y → Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L →
        (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        (∀ m ∈ S,‖α m‖ ≤ L^Cα) → (∀ n ∈ Icc l r,‖β n‖ ≤ L^Cβ) →
        let W := Real.exp (L^(6/25:ℝ))
        (∀ m ∈ S,α m ≠ 0 → MarkedPhysicalRoughAt W m) →
        (∀ n ∈ Icc l r,β n ≠ 0 → MarkedPhysicalRoughAt W n) →
        (∀ (k : ℕ) [NeZero k], (k:ℝ) ≤ L^a → ∀ χ : DirichletCharacter ℂ k,∀ t : ℝ,
          |t| ≤ 2*(H*U)*L^(a+2) → ‖markedTwistedSum S α χ t‖/H ≤ L^(-R)) →
        ‖markedTypeIIScalarFullMajor (fun j => markedLogPowerBand (e j) (Real.exp L))
          S (Icc l r) markedTypeIILabelCutoff markedTypeIIDeterminantCutoff (L^a) Y α β‖ ≤
          (Y*(H*U))*L^(-D) := by
  let E := Equiv.optionSubtypeNe i₀
  let η := markedTypeIILabelCutoff
  let ψ := markedTypeIIDeterminantCutoff
  let v₀ := Real.log 2/2
  let D' := D+3*a+1+6*a
  have hv₀ : 0 < v₀ := by dsimp only [v₀]; positivity
  have hD' : 0 ≤ D' := by dsimp only [D']; linarith
  obtain ⟨R,hR,henergy⟩ := markedMajorScalarMellin_all_log η markedTypeIILabelCutoff_contDiff
    markedTypeIILabelCutoff_norm_le_one markedTypeIILabelCutoff_support ψ markedTypeIIDeterminantCutoff_tsupport
    1 2 δ 2 a Cα Cβ D' Kx v₀ zero_lt_one (by norm_num) hδ (by norm_num) ha hCα hCβ hD' hv₀
  refine ⟨R,hR,?_⟩
  filter_upwards [henergy,markedMajorTypeII_band_data e hinj he a,
    marked_polynomial_le_exp_rpow 2 a (6/25) (by norm_num),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop Kx),
    eventually_ge_atTop (4:ℝ)] with L henergy hband hrough hK hL
  intro Y H U S l r α β hY hH hU hX hS hl hr hα hβ
  dsimp only
  intro hrα hrβ hlong
  let P := fun j => markedLogPowerBand (e j) (Real.exp L)
  let P₀ := P (E none)
  let bands := fun j : {j : I // j ≠ i₀} => P (E (some j))
  let P' := fun j : Option {j : I // j ≠ i₀} => j.elim P₀ bands
  have hP' : P' = fun j => P (E j) := by
    funext j
    cases j <;> rfl
  have hLp : 0 < L := (by norm_num : (0:ℝ)<4).trans_le hL
  have hHp := (Real.exp_pos _).trans_le hH
  have hUp := (Real.exp_pos _).trans_le hU
  have hXp := mul_pos hHp hUp
  have hExp := Real.one_le_exp (mul_nonneg hδ.le hLp.le)
  have hX₁ : 1 ≤ H*U := one_le_mul_of_one_le_of_one_le (hExp.trans hH) (hExp.trans hU)
  have hX₂ : H*U ≤ Real.exp (2*L) := by
    calc
      _ ≤ Kx*Real.exp L := hX
      _ ≤ Real.exp L*Real.exp L := mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, two_mul]
  have hQ : 0 < L^a := Real.rpow_pos_of_pos hLp _
  have hQW : L^a < Real.exp (L^(6/25:ℝ)) := by linarith
  have hP₀ (p : ℕ) (hp : p∈P₀) : p.Prime := (hband.2.1 (E none) p hp).1
  have hb (j : {j : I // j ≠ i₀}) (p : ℕ) (hp : p∈bands j) : p.Prime :=
    (hband.2.1 (E (some j)) p hp).1
  have hdis₀ (j : {j : I // j ≠ i₀}) : Disjoint P₀ (bands j) := by
    apply hband.1
    intro h
    have hn : (none : Option {j : I // j ≠ i₀}) = some j := E.injective h
    cases hn
  have hdis : Pairwise (fun i j => Disjoint (bands i) (bands j)) :=
    fun _ _ hij => hband.1 (fun h => hij (Option.some.inj (E.injective h)))
  have hV₀ : v₀ ≤ bandReciprocalMass P₀ := hband.2.2.1 (E none)
  have hV (j : {j : I // j ≠ i₀}) : 0 < bandReciprocalMass (bands j) :=
    hv₀.trans_le (hband.2.2.1 (E (some j)))
  have hlo (p : ℕ) (hp : p∈P₀) : 1*L^(1/(10:ℝ)) ≤ Real.log p := by
    simpa only [one_mul] using (hband.2.1 (E none) p hp).2.1
  have hhi (p : ℕ) (hp : p∈P₀) : Real.log p ≤ 2*L^(1/(5:ℝ)) :=
    (hband.2.1 (E none) p hp).2.2
  have hP (j : Option {j : I // j ≠ i₀}) (p : ℕ) (hp : p∈P' j) : p.Prime := by
    rw [hP'] at hp
    exact (hband.2.1 (E j) p hp).1
  have hbandQ (j : Option {j : I // j ≠ i₀}) (p : ℕ) (hp : p∈P' j) : L^a < (p:ℝ) := by
    rw [hP'] at hp
    exact hband.2.2.2 (E j) p hp
  have hT (n : ℕ) (hn : n∈Icc l r) : U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U :=
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hr⟩
  have hmajor :
      ‖markedTypeIIScalarFullMajor P' S (Icc l r) η ψ (L^a) Y α β‖ ≤ (Y*(H*U))*L^(-D) := by
    apply markedTypeIIScalarFullMajor_norm_of_character_terms P' η ψ S (Icc l r) α β
      hL hXp hY hQ.le le_rfl hQW markedTypeIILabelCutoff_support hP hbandQ hrα hrβ
    intro q _ hq χ θ hθ
    have hM := henergy P₀ bands hP₀ hb hdis₀ hdis hV₀ hV hlo hhi
      Y H U S l r α β hY hHp hUp hU hX₁ hX₂ hX hS hl hr hα hβ hlong q hq χ θ hθ
    exact (markedMajorScalarArcCharacterTerm_norm_le P' η ψ markedTypeIIDeterminantCutoff_tsupport
      hY hHp hUp markedTypeIILabelCutoff_support S (Icc l r) α β hS hT q χ θ).trans
      (mul_le_mul_of_nonneg_left hM (mul_pos hY hXp).le)
  rw [hP',markedTypeIIScalarFullMajor_reindex E P] at hmajor
  exact hmajor

end
end ArtinMatthews
