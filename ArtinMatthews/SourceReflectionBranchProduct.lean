module

public import ArtinMatthews.SourceReflectionClassSlices
public import Mathlib.Topology.Algebra.InfiniteSum.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The actual supported branch with its finite retained labels can be
read either as one product series or as a finite sum in each frequency. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} [Fintype U]
variable [Fintype (SWholePowerClasses F 6 (sourceHilbertSet F S₀))]

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "Q" => SWholePowerClasses F 6 (sourceHilbertSet F S₀)
local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ
local notation "T" => sourceReflectionExpansionTerm F S₀ hζ

theorem sourceReflectionSupportedBranch_tsum_prod
    (A : SourceReflectionExpansionData F S₀ (U × Q × Q))
    {Z : ℝ} (hZ : 0 < Z) (h d : E) (f : Finset Prime) :
    (∑' p : SourceReflectionSupportedTermIndex F S₀ f d × U,
      T A Z h d f p.1.val.1.val p.1.val.2.1 p.1.val.2.2.val
        (p.2, C d, C p.1.val.2.2.val)) =
    ∑' i : SourceReflectionSupportedTermIndex F S₀ f d,
      ∑ j : U, T A Z h d f i.val.1.val i.val.2.1 i.val.2.2.val
        (j, C d, C i.val.2.2.val) := by
  let B := sourceReflectionExpansionData_withClassSlices F S₀ hζ A
  let I := SourceReflectionTermIndex F S₀ f
  let P := SourceReflectionSupportedTermIndex F S₀ f d × U
  let g (p : (U × Q × Q) × I) := T B Z h d f p.2.1.val p.2.2.1 p.2.2.2.val p.1
  let ι (p : P) : (U × Q × Q) × I := ((p.2, C d, C p.1.val.2.2.val), p.1.val)
  have hi : Function.Injective ι := by
    intro p q hp
    exact Prod.ext (Subtype.ext (congrArg Prod.snd hp))
      (congrArg (fun x : (U × Q × Q) × I => x.1.1) hp)
  have hg : Summable (fun p => ‖g p‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
    exact ⟨fun j => sourceReflectionExpansionTerm_norm_summable F S₀ hζ B hZ h d f j,
      Summable.of_finite⟩
  have he (p : P) : g (ι p) =
      T A Z h d f p.1.val.1.val p.1.val.2.1 p.1.val.2.2.val
        (p.2, C d, C p.1.val.2.2.val) := by
    dsimp only [g, ι, B]
    simp [sourceReflectionExpansionTerm_withClassSlices, sourceReflectionClassIndicator]
  have hs : Summable (fun p : P => T A Z h d f p.1.val.1.val p.1.val.2.1 p.1.val.2.2.val
        (p.2, C d, C p.1.val.2.2.val)) :=
    ((hg.comp_injective hi).of_norm).congr he
  rw [hs.tsum_prod]
  exact tsum_congr (fun _ => tsum_fintype _)

end
end ArtinMatthews.SourceEulerAssembly
