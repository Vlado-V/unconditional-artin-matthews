module

public import ArtinMatthews.SourceKPCompactRationalTransport
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPCuspArchRepresentative
public import ArtinMatthews.SourceKPTranslateGramCompactAE
public import ArtinMatthews.SourceKPAdelicUpperAE


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth native representatives descend by the rational chart relation
and the full support of the actual archimedean Haar measure. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "Ω" => productUpper V
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "B" => SourceKPFiniteLevelFiber K hζ
local notation "H" => SourceKPArchUpperHalfSpace K
local notation "π" => sourceKPUpperToCompact K hζ
local notation "ι" => sourceKPArchUpperEuclideanMap K
local notation "ν" => sourceKPArchHyperbolicMeasure K

theorem sourceKPCompactUpperCharts_surjective :
    Function.Surjective (fun x : B × H => π x.1 x.2) := by
  intro y
  obtain ⟨q,rfl⟩ := Quotient.mk_surjective y
  obtain ⟨⟨a,b⟩,rfl⟩ := Quotient.mk_surjective q
  exact ⟨(b,sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)),
    sourceKPUpperToCompact_mk K hζ b a⟩

private theorem lift_ae (R : Y → ℂ) (b : B) (U : X → ℂ)
    (hU : U =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ R b) :
    (fun p : H => U (ι p)) =ᵐ[ν] fun p : H => R (π b p) := by
  have ha := (sourceKPArchUpperEuclideanMap_preserving K).quasiMeasurePreserving.ae_eq_comp hU
  filter_upwards [ha] with p hp
  have hpos : ι p ∈ Ω := fun v _ => SourceArchJacquet.sourceArchUpperEuclideanMap_positive (p v)
  exact hp.trans (by rw [Function.comp_apply,sourceKPCompactChartPullback_of_positive K hζ R b _ hpos,
    sourceKPArchUpperEuclideanMap_left_inverse])

theorem sourceKPCompactSmoothCharts_consistent (R : Y → ℂ) (U : B → X → ℂ)
    (hU : ∀ b, ContinuousOn (U b) Ω)
    (hUae : ∀ b, U b =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ R b)
    (b c : B) (p q : H) (h : π b p = π c q) :
    U b (ι p) = U c (ι q) := by
  obtain ⟨γ,rfl,rfl⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ b c p q).mp h
  let A := sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ)
  have hA : Continuous A := sourceKPArchUpperAction_continuous K hζ _
  have hc (b : B) : Continuous (fun p : H => U b (ι p)) :=
    (hU b).comp_continuous (sourceKPArchUpperEuclideanMap_continuous K)
      (fun p v _ => SourceArchJacquet.sourceArchUpperEuclideanMap_positive (p v))
  have h₁ := (sourceKPArchUpperAction_preserving K hζ
    (sourceKPRationalArchMap K hζ γ)).quasiMeasurePreserving.ae_eq_comp
      (lift_ae K hζ R (γ • c) (U (γ • c)) (hUae (γ • c)))
  have h₂ := lift_ae K hζ R c (U c) (hUae c)
  have he : (fun x : H => U (γ • c) (ι (A x))) =ᵐ[ν] fun x : H => U c (ι x) := by
    filter_upwards [h₁,h₂] with x hx hy
    change U (γ • c) (ι (A x)) = R (π (γ • c) (A x)) at hx
    rw [sourceKPUpperToCompact_rational K hζ γ c x] at hx
    exact hx.trans hy.symm
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq he ((hc _).comp hA) (hc _)) q

theorem sourceKPCompactSmoothRepresentative_exists (R : Y → ℂ) (U : B → X → ℂ)
    (hU : ∀ b, ContDiffOn ℝ (∞ : ℕ∞ω) (U b) Ω)
    (hUae : ∀ b, U b =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ R b) :
    ∃ W : Y → ℂ, W =ᵐ[sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)] R ∧
      (∀ b, ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ W b) Ω) ∧
      (∀ b, Set.EqOn (sourceKPCompactChartPullback K hζ W b) (U b) Ω) := by
  classical
  choose r hr using sourceKPCompactUpperCharts_surjective K hζ
  let W : Y → ℂ := fun y => U (r y).1 (ι (r y).2)
  have hw (b : B) (p : H) : W (π b p) = U b (ι p) :=
    sourceKPCompactSmoothCharts_consistent K hζ R U (fun c => (hU c).continuousOn) hUae
      (r (π b p)).1 b (r (π b p)).2 p (hr _)
  have he (b : B) : Set.EqOn (sourceKPCompactChartPullback K hζ W b) (U b) Ω := by
    intro p hp
    rw [sourceKPCompactChartPullback_of_positive K hζ W b p hp,
      hw b (sourceKPArchEuclideanUpperMap K p),
      sourceKPArchUpperEuclideanMap_right_inverse K p (productUpper_pos hp)]
  refine ⟨W,?_,fun b => (hU b).congr (he b),he⟩
  apply sourceKPFiniteLevelToCompact_ae_of_comp K hζ
  apply (sourceKPFiniteRepresentative_ae_iff_slices K hζ _).mpr
  intro b
  have ha := (sourceKPCuspArchRepresentativeCoordinates_measurePreserving K hζ).quasiMeasurePreserving.ae_eq_comp
    (hUae b)
  filter_upwards [ha] with a ha
  let p := sourceKPCuspArchRepresentativeCoordinates K hζ a
  have hp : p ∈ Ω := fun v _ => SourceArchJacquet.sourceArchUpperEuclideanMap_positive _
  have hπ : sourceKPFiniteLevelToCompact K hζ (a,b) =
      π b (sourceKPArchEuclideanUpperMap K p) := by
    dsimp only [p, sourceKPCuspArchRepresentativeCoordinates]
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    exact (sourceKPUpperToCompact_mk K hζ b a).symm
  change W (sourceKPFiniteLevelToCompact K hζ (a,b)) = R (sourceKPFiniteLevelToCompact K hζ (a,b))
  rw [hπ,hw,sourceKPArchUpperEuclideanMap_right_inverse K p (productUpper_pos hp)]
  exact ha.trans (sourceKPCompactChartPullback_of_positive K hζ R b p hp)

end
end ArtinMatthews
