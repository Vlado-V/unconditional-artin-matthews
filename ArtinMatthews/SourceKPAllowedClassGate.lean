module

public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.SourceKPRetainedTinySixth
public import ArtinMatthews.SourceThetaFiniteMellin
public import ArtinMatthews.SLocalNormOneGroup
public import Mathlib.Topology.Algebra.OpenSubgroup


set_option backward.privateInPublic true
@[expose] public section

/-! The positive side uses the original whole local unit group and the
actual chosen complement to the S-unit image. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open AllowedGenerators SourcePhysical SourceReflection Filter
open scoped NumberField Topology Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "Pr" => HeightOneSpectrum (𝓞 K)

/-- The literal ring sixth-power class on the product of the whole local units. -/
def sourceKPWholeSixthClass (S : Finset Pr) : SWholeUnits K S →* SLocalRingPowerClasses K 6 S :=
  (sLocalRingPowerEquiv K 6 S).symm.toMonoidHom.comp (QuotientGroup.mk' _)

@[simp] theorem sourceKPWholeSixthClass_diagonal (S : Finset Pr) (m : Kˣ) :
    sourceKPWholeSixthClass K S (sWholeDiagonal K S m) = sLocalRingGlobalClassMap K 6 S m := by
  change (sLocalRingPowerEquiv K 6 S).symm (sWholeGlobalClassMap K 6 S m) = _
  rw [← sLocalRingPowerEquiv_globalClass, MulEquiv.symm_apply_apply]

@[simp] theorem sourceKPWholeSixthClass_sixth (S : Finset Pr) (x : SWholeUnits K S) :
    sourceKPWholeSixthClass K S (x^6) = 1 := by
  have h : (QuotientGroup.mk'
      (powMonoidHom ((6 : ℕ+) : ℕ) : SWholeUnits K S →* SWholeUnits K S).range) (x^6) = 1 :=
    (QuotientGroup.eq_one_iff (x^6)).mpr ⟨x, rfl⟩
  change (sLocalRingPowerEquiv K 6 S).symm _ = 1
  rw [h, map_one]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

include hζ in
theorem sourceKPWholeSixthClass_eq_one_of_finite_sixth (S : Finset Pr) (x : SWholeUnits K S)
    (hx : ∀ P : S, ∃ w : (P.val.adicCompletion K)ˣ, w^6 = x.2 P) :
    sourceKPWholeSixthClass K S x = 1 := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := sWholePowerEquiv K 6 S
  have he : (QuotientGroup.mk'
      (powMonoidHom ((6 : ℕ+) : ℕ) : SWholeUnits K S →* SWholeUnits K S).range) x = 1 := by
    apply e.injective
    rw [show e = sWholePowerEquiv K 6 S from rfl, sWholePowerEquiv_mk, map_one]
    funext P
    obtain ⟨w, hw⟩ := hx P
    rw [← hw]
    exact (QuotientGroup.eq_one_iff (w^6)).mpr ⟨w, rfl⟩
  change (sLocalRingPowerEquiv K 6 S).symm _ = 1
  rw [he, map_one]

include hζ in
private theorem sourceKPWholeSixthClass_eventually_one (S : Finset Pr) :
    ∀ᶠ x : SWholeUnits K S in 𝓝 1, sourceKPWholeSixthClass K S x = 1 := by
  choose M _ hroot using fun P : S => sourceKPRetained_tiny_sixth K P.val
  have hn (P : S) : ∀ᶠ x : SWholeUnits K S in 𝓝 1,
      ((x.2 P : P.val.adicCompletion K) - 1) ∈ sourceLocalBall K P.val (-(M P : ℤ)) := by
    let f (x : SWholeUnits K S) : P.val.adicCompletion K := (x.2 P : P.val.adicCompletion K) - 1
    have hf : Continuous f := (Units.continuous_val.comp
      ((continuous_apply P).comp continuous_snd)).sub continuous_const
    have h1 : f 1 = 0 := sub_self 1
    have h0 : f 1 ∈ sourceLocalBall K P.val (-(M P : ℤ)) := by
      rw [h1]
      exact (sourceLocalOpenBall K P.val (-(M P : ℤ))).zero_mem
    exact hf.continuousAt ((sourceLocalBall_isOpen K P.val _).mem_nhds h0)
  filter_upwards [eventually_all.mpr hn] with x hx
  exact sourceKPWholeSixthClass_eq_one_of_finite_sixth K hζ S x (fun P => hroot P _ (hx P))

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
include hζ S₀
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "C" => sourceKPWholeSixthClass K S
local notation "B" => (chosenB K hζ S₀)
local notation "Γ" => sNormOneSixthSubgroup K S

theorem sourceKPAllowedClass_finite : Finite (SLocalRingPowerClasses K 6 S) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let : Finite (SLocalPowerClasses K 6 S) := sLocalBilinearForm_finite K 6
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S
    (normSupport_subset_sourceHilbertSet K S₀ 6 (Or.inr (Or.inr rfl)))
  exact Finite.of_equiv _ ((sLocalRingPowerEquiv K 6 S).trans (sWholePowerEquiv K 6 S)).toEquiv.symm

/-- The positive gate is the characteristic function of the chosen complement. -/
def sourceKPAllowedClassGate (x : U) : ℂ := if C x ∈ B then 1 else 0

theorem sourceKPAllowedClassGate_support_open : IsOpen {x : U | C x ∈ B} := by
  change IsOpen ((Subgroup.comap C B : Subgroup U) : Set U)
  apply (Subgroup.comap C B).isOpen_of_mem_nhds (g := 1)
  filter_upwards [sourceKPWholeSixthClass_eventually_one K hζ S] with x hx
  change C x ∈ B
  rw [hx]
  exact (B).one_mem

theorem sourceKPAllowedClassGate_measurable [MeasurableSpace U] [BorelSpace U] :
    Measurable (sourceKPAllowedClassGate K hζ S₀) := by
  change Measurable ({x : U | C x ∈ B}.indicator (fun _ : U => (1 : ℂ)))
  exact measurable_const.indicator (sourceKPAllowedClassGate_support_open K hζ S₀).measurableSet

@[simp] theorem sourceKPAllowedClassGate_diagonal (m : Kˣ) :
    sourceKPAllowedClassGate K hζ S₀ (sWholeDiagonal K S m) =
      if m ∈ allowedSubgroup K hζ S₀ then 1 else 0 := by
  simp only [sourceKPAllowedClassGate, sourceKPWholeSixthClass_diagonal, mem_allowedSubgroup]

theorem sourceKPAllowedClassGate_gamma (x : U) (γ : Γ) :
    sourceKPAllowedClassGate K hζ S₀ (x * (γ.val : U)) =
      sourceKPAllowedClassGate K hζ S₀ x := by
  obtain ⟨u, hu⟩ := γ.property
  have he := congrArg (fun z : SNormOne K S => (z : U)) hu
  rw [sNormOneSixthMap_val, map_pow] at he
  have hc : C (x * (γ.val : U)) = C x := by
    rw [← he, map_mul, sourceKPWholeSixthClass_sixth]
    exact mul_one (C x)
  unfold sourceKPAllowedClassGate
  rw [hc]

theorem sourceKPWholeSixthClass_inv_of_retainedProduct_ne_zero
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region → ∃ w, w^6 = t)
    (m : Kˣ) (x : U)
    (hb : (∏ P : S, (W P).factor ((sWholeDiagonal K S m * x).2 P)) ≠ 0) :
    C x = (sLocalRingGlobalClassMap K 6 S m)⁻¹ := by
  let z := sWholeDiagonal K S m * x
  have hz (P : S) : z.2 P ∈ (W P).region := by
    by_contra hn
    exact hb (Finset.prod_eq_zero (Finset.mem_univ P) (Set.indicator_of_notMem hn _))
  have hz₁ : C z = 1 :=
    sourceKPWholeSixthClass_eq_one_of_finite_sixth K hζ S z (fun P => hW P _ (hz P))
  have hm : C (sWholeDiagonal K S m) * C x = 1 := (map_mul C _ _).symm.trans hz₁
  calc
    _ = (C (sWholeDiagonal K S m))⁻¹ * (C (sWholeDiagonal K S m) * C x) :=
      (inv_mul_cancel_left _ _).symm
    _ = _ := by
      rw [hm, sourceKPWholeSixthClass_diagonal]
      exact mul_one ((sLocalRingGlobalClassMap K 6 S m)⁻¹)

theorem sourceKPAllowedClassGate_mul_retainedProduct
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region → ∃ w, w^6 = t)
    (m : Kˣ) (x : U) :
    sourceKPAllowedClassGate K hζ S₀ x *
      (∏ P : S, (W P).factor ((sWholeDiagonal K S m * x).2 P)) =
      if m ∈ allowedSubgroup K hζ S₀ then
        ∏ P : S, (W P).factor ((sWholeDiagonal K S m * x).2 P) else 0 := by
  let b := ∏ P : S, (W P).factor ((sWholeDiagonal K S m * x).2 P)
  change sourceKPAllowedClassGate K hζ S₀ x * b =
    if m ∈ allowedSubgroup K hζ S₀ then b else 0
  by_cases hb : b = 0
  · simp [hb]
  · have hc := sourceKPWholeSixthClass_inv_of_retainedProduct_ne_zero K hζ S₀ W hW m x hb
    have ha : C x ∈ B ↔ m ∈ allowedSubgroup K hζ S₀ := by
      rw [hc, (B).inv_mem_iff, mem_allowedSubgroup]
    by_cases h : m ∈ allowedSubgroup K hζ S₀ <;> simp [sourceKPAllowedClassGate, ha, h]

end
end ArtinMatthews
