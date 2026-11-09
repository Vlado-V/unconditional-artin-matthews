module

public import ArtinMatthews.SourceKPAllowedForwardSeries
public import ArtinMatthews.SourceKPAllowedSquarefreeCube
public import ArtinMatthews.SourceKPRetainedExteriorWhittaker
public import ArtinMatthews.SourceSLocalQuotientSheet


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exterior Whittaker support removes the unsupported field
frequencies. The retained squarefree and cube coefficients periodize
over the distinct norm-one sixth-power image. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical SourceReflection
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "I" => (C × E) × Γ
local notation "A" => allowedSubgroup K hζ S₀
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "good" => sourceKPPositiveCubeSupport K S₀
local notation "freq" => sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀

theorem sourceKPRetainedExteriorWhittaker_zero_off_allowed_support
    (hS : standardWeilBadPlaces K ⊆ S) (m : Kˣ) (ha : m ∈ A)
    (hm : m ∉ sourceKPAllowedFieldSupport K hζ S₀ good) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS m = 0 := by
  by_contra hW
  have h (P : SourceExteriorPrime K S₀) :=
    sourceKPRetainedExteriorWhittaker_nonzero_orders K hζ S₀ hS m hW P
  apply hm
  refine sourceKPAllowedSquarefreeCube_mem_of_orders K hζ S₀ m ha (fun P => (h P).1) ?_
  intro P
  have hn := (h P).2
  omega

def sourceKPAllowedPositiveOrbitTerm (G : C → E → U → ℂ) (p : I) (x : U) : ℂ :=
  G p.1.1 p.1.2 (sWholeDiagonal K S (gen (p.1.1.val + 3 • p.1.2)) * p.2.val.val * x)

theorem sourceKPAllowedPositiveOrbitTerm_tsum_gamma (G : C → E → U → ℂ) (x : U) (δ : Γ) :
    (∑' p : I, sourceKPAllowedPositiveOrbitTerm K hζ S₀ G p (x * δ.val.val)) =
      ∑' p : I, sourceKPAllowedPositiveOrbitTerm K hζ S₀ G p x := by
  let e : I ≃ I := (Equiv.refl (C × E)).prodCongr (Equiv.mulRight δ)
  calc
    _ = ∑' p : I, sourceKPAllowedPositiveOrbitTerm K hζ S₀ G (e p) x := by
      apply tsum_congr
      rintro ⟨⟨c,n⟩,γ⟩
      change G c n (sWholeDiagonal K S (gen (c.val + 3 • n)) * γ.val.val * (x * δ.val.val)) =
        G c n (sWholeDiagonal K S (gen (c.val + 3 • n)) * (γ.val.val * δ.val.val) * x)
      congr 1
      ac_rfl
    _ = _ := e.tsum_eq (fun p : I => sourceKPAllowedPositiveOrbitTerm K hζ S₀ G p x)

local notation "Wext[" h "]" => sourceKPRetainedExteriorWhittaker K hζ S₀ h

theorem sourceKPAllowedSquarefreeCubeFieldEquiv_exteriorWhittaker
    (hS : standardWeilBadPlaces K ⊆ S)
    (c : C) (n : E) (γ : Γ) :
    Wext[hS] (freq ((c,n),γ)).val =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
          (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  obtain ⟨u,hu⟩ := sourceExteriorUnitSixthPower_exists_root S
    ((sourceExteriorSixthNormOneEquiv K S).symm γ)
  have he := congrArg (fun v : exteriorUnitSubgroup S => v.val) hu
  rw [sourceKPAllowedSquarefreeCubeFieldEquiv_fieldUnit, he, Subgroup.coe_pow]
  exact sourceKPRetainedExteriorWhittaker_squarefree_cube_mul_sixth K hζ S₀ hS c n u

theorem sourceKPAllowedForwardSquarefreeCube_hasSum
    (hS : standardWeilBadPlaces K ⊆ S)
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region → ∃ w, w^6 = t)
    (H : Kˣ → U → ℂ) (G : C → E → U → ℂ)
    (hG : ∀ (c : C) (n : E) (γ : Γ) (z : U),
      let m := (freq ((c,n),γ)).val
      (Wext[hS] m * H m z) * (∏ P : S, (W P).factor (z.2 P)) = G c n z)
    (x : U) {s₀ : ℂ}
    (hs : HasSum (fun m => sourceKPForwardRetainedTerm K S₀ W (fun m z => Wext[hS] m * H m z) m x) s₀) :
    HasSum (fun p : I => sourceKPAllowedPositiveOrbitTerm K hζ S₀ G p x)
      (sourceKPAllowedClassGate K hζ S₀ x * s₀) := by
  let F (m : Kˣ) (z : U) := Wext[hS] m * H m z
  let f (m : Kˣ) := if m ∈ A then sourceKPForwardRetainedTerm K S₀ W F m x else 0
  have hf : HasSum f (sourceKPAllowedClassGate K hζ S₀ x * s₀) :=
    sourceKPAllowedClassGate_hasSum K hζ S₀ W hW F x hs
  have hzero (m : Kˣ) (hm : m ∉ sourceKPAllowedFieldSupport K hζ S₀ good) : f m = 0 := by
    by_cases ha : m ∈ A
    · have he := sourceKPRetainedExteriorWhittaker_zero_off_allowed_support K hζ S₀ hS m ha hm
      simp only [f, ite_eq_left ha, sourceKPForwardRetainedTerm, F, he, zero_mul]
    · exact ite_eq_right ha
  have hb := sourceKPAllowedSquarefreeCube_hasSum K hζ S₀ hf hzero
  apply hb.congr_fun
  rintro ⟨⟨c,n⟩,γ⟩
  let m := freq ((c,n),γ)
  have ha : m.val ∈ A := m.property.1
  change sourceKPAllowedPositiveOrbitTerm K hζ S₀ G ((c,n),γ) x = f m.val
  simp only [f, ite_eq_left ha, sourceKPAllowedPositiveOrbitTerm, sourceKPForwardRetainedTerm, F]
  rw [sourceKPAllowedSquarefreeCubeFieldEquiv_diagonal K hζ S₀ c n γ]
  exact (hG c n γ _).symm

theorem sourceKPAllowedForwardSeries_sixthInvariant
    (hS : standardWeilBadPlaces K ⊆ S)
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region → ∃ w, w^6 = t)
    (H : Kˣ → U → ℂ) (G : C → E → U → ℂ)
    (hG : ∀ (c : C) (n : E) (γ : Γ) (z : U),
      let m := (freq ((c,n),γ)).val
      (Wext[hS] m * H m z) * (∏ P : S, (W P).factor (z.2 P)) = G c n z)
    (hs : ∀ x : U, Summable (fun m =>
      sourceKPForwardRetainedTerm K S₀ W (fun m z => Wext[hS] m * H m z) m x)) :
    sourceSLocalSixthInvariant S
      (sourceKPAllowedForwardSeries K hζ S₀ W (fun m z => Wext[hS] m * H m z)) := by
  let F (m : Kˣ) (z : U) := Wext[hS] m * H m z
  have hval (x : U) : (∑' p : I, sourceKPAllowedPositiveOrbitTerm K hζ S₀ G p x) =
      sourceKPAllowedForwardSeries K hζ S₀ W F x :=
    (sourceKPAllowedForwardSquarefreeCube_hasSum K hζ S₀ hS W hW H G hG x (hs x).hasSum).tsum_eq
  intro x δ
  change sourceKPAllowedForwardSeries K hζ S₀ W F (x * δ.val.val) =
    sourceKPAllowedForwardSeries K hζ S₀ W F x
  rw [← hval (x * δ.val.val), ← hval x]
  exact sourceKPAllowedPositiveOrbitTerm_tsum_gamma K hζ S₀ G x δ

end
end ArtinMatthews
