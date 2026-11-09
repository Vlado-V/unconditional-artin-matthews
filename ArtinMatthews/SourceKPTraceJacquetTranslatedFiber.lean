module

public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber
public import ArtinMatthews.SourceKPTraceJacquetLocalTranslate


set_option backward.privateInPublic true
@[expose] public section

/-! A general right translate in the actual weighted finite fiber.
The local component is split in the covering group, and its entire
translated value is evaluated on the literal coupled rest. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "G" => SourceKPAdelicProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "κ₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P.val
local notation "F₀" => sourceKPAdelicCompactSection K hζ
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "base₀" => sourceKPAdelicLocalBase K hζ P.val
local notation "single₀" => sourceKPFiniteAdditiveSingle K P.val

theorem sourceKPTraceJacquetGlobalFiber_split_right (g : G) :
    ∃ (q : G₀) (g₀ : G), base₀ g₀ = 1 ∧ g = ι₀ q*g₀ := by
  obtain ⟨q,hq⟩ := sourceFiniteKP2ProjectiveProjection_surjective K hζ P.val (base₀ g)
  refine ⟨q,(ι₀ q)⁻¹*g,?_,?_⟩
  · rw [map_mul, map_inv, sourceKPAdelicLocalBase_local, hq, inv_mul_cancel]
  · rw [mul_inv_cancel_left]

theorem sourceKPTraceJacquetGlobalFiber_factor_translated
    (x : L) (r : 𝔸ᶠ[K]) (hr : r P.val = 0) (q : G₀) (g₀ : G) (hg₀ : base₀ g₀ = 1) :
    W₀ * sourceKPAdelicUpperLift K hζ (0,single₀ x+r) * (ι₀ q*g₀) =
      ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x) * q) *
        sourceKPLocalFiberRest K hζ P.val r g₀ := by
  let R := sourceKPLocalFiberRest K hζ P.val r g₀
  have hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val q g₀ hg₀
  have hcR := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val q R hR
  rw [hc.eq, ← mul_assoc, sourceKPLocalFiber_factor K hζ P.val x r g₀, mul_assoc, ← hcR.eq, ← mul_assoc,
    ← map_mul]

theorem sourceKPTraceJacquetLocalRest_translated_integral
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (m : Lˣ)
    (q : G₀) (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hq : q = z₀ z * l₀ (sourceGL2Upper u) * l₀ (sourceGL2Diagonal y) * κ₀ k)
    (R : G) (hR : base₀ R = 1) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (fun x : L => ψ₀ (-((m : L)*x)) *
      ((F₀ s).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)*q)*R)).val t) μ₀ ∧
    (∫ x : L, ψ₀ (-((m : L)*x)) *
      ((F₀ s).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)*q)*R)).val t ∂μ₀) =
      sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s R hR) t
        (sourceKPTraceJacquetLocalTranslatedValue K hζ S₀ P s m z u y) := by
  let v := sourceKPLocalRestVector K hζ S₀ P s R hR
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s v t
  let I := sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m q
  have hI := sourceKPTraceJacquetLocalTranslated_integral K hζ S₀ P hP hs m q z u y k hq
  have he (x : L) : ψ₀ (-((m : L)*x)) *
      ((F₀ s).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)*q)*R)).val t = A (I x) := by
    rw [sourceKPLocalRest_section K hζ S₀ P s R hR, sourceKPLocalReceiverIntertwining_apply]
    change _ = A (sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m q x)
    rw [sourceKPTraceJacquetLocalTranslatedIntegrand, map_smul]
    rfl
  refine ⟨(A.integrable_comp hI.1).congr (Filter.Eventually.of_forall fun x => (he x).symm),?_⟩
  simp_rw [he]
  rw [A.integral_comp_comm hI.1]
  exact congrArg A hI.2

theorem sourceKPTraceJacquetGlobalFiber_translated_integral
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (m : Kˣ)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) (q : G₀) (g₀ : G) (hg₀ : base₀ g₀ = 1)
    (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hq : q = z₀ z * l₀ (sourceGL2Upper u) * l₀ (sourceGL2Diagonal y) * κ₀ k)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    let R := sourceKPLocalFiberRest K hζ P.val r g₀
    let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
    Integrable (fun x : L => sourceKPTraceJacquetFiniteCharacter K m (single₀ x+r) *
      ((F₀ s).val (W₀ * sourceKPAdelicUpperLift K hζ (0,single₀ x+r)*(ι₀ q*g₀))).val t) μ₀ ∧
    (∫ x : L, sourceKPTraceJacquetFiniteCharacter K m (single₀ x+r) *
      ((F₀ s).val (W₀ * sourceKPAdelicUpperLift K hζ (0,single₀ x+r)*(ι₀ q*g₀))).val t ∂μ₀) =
      sourceKPTraceJacquetFiniteCharacter K m r *
        sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s R hR) t
          (sourceKPTraceJacquetLocalTranslatedValue K hζ S₀ P s
            (sourceKPTraceJacquetFrequencyAt K P.val m) z u y) := by
  let R := sourceKPLocalFiberRest K hζ P.val r g₀
  let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
  let mP := sourceKPTraceJacquetFrequencyAt K P.val m
  let C := sourceKPTraceJacquetFiniteCharacter K m r
  let I := fun x : L => ψ₀ (-((mP : L)*x)) *
    ((F₀ s).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)*q)*R)).val t
  have he (x : L) : sourceKPTraceJacquetFiniteCharacter K m (single₀ x+r) *
      ((F₀ s).val (W₀ * sourceKPAdelicUpperLift K hζ (0,single₀ x+r)*(ι₀ q*g₀))).val t = C*I x := by
    rw [sourceKPTraceJacquetFiniteCharacter_single_add K P.val m x r,
      sourceKPTraceJacquetGlobalFiber_factor_translated K hζ S₀ P x r hr q g₀ hg₀,
      sourceKPTraceJacquetFinitePhase_star_eq_neg K]
    change (ψ₀ (-((mP : L)*x))*C) *
      ((F₀ s).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)*q)*R)).val t = _
    dsimp only [I]
    ring
  have h := sourceKPTraceJacquetLocalRest_translated_integral K hζ S₀ P hP hs mP q z u y k hq R hR t
  refine ⟨(h.1.const_mul C).congr (Filter.Eventually.of_forall fun x => (he x).symm),?_⟩
  conv_lhs => simp only [he]
  rw [integral_const_mul]
  exact congrArg (C*·) h.2

end
end ArtinMatthews
