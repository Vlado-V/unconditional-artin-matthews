module

public import ArtinMatthews.SourceKPLocalRootCenter
public import ArtinMatthews.SourceKPLocalFiberFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The rational Weyl element takes the actual single-place upper
lift to its lower lift. Thus any subgroup containing the finite
upper group and rational Weyl element contains a nontrivial genuine
central element. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G" => SourceKPAdelicProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "N₀" => sourceKPAdelicUpperLift K hζ
local notation "single₀" => sourceKPFiniteAdditiveSingle K P

theorem sourceKPAdelicRootWeyl_conj_single (x : L) :
    W₀*N₀ (0,single₀ x)*W₀⁻¹ = ι₀ (l₀ (sourceGL2Lower x)) := by
  let w := ι₀ (l₀ sourceGL2Weyl)
  let n := ι₀ (l₀ (sourceGL2Upper x))
  let r := w⁻¹*W₀
  have hr : sourceKPAdelicLocalBase K hζ P r = 1 := sourceKPLocalWeylRest_base K hζ P
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P (l₀ (sourceGL2Upper x)) r hr
  have hw : W₀ = w*r := by
    dsimp only [r]
    rw [mul_inv_cancel_left]
  have hw₂ : w*w = 1 := by
    dsimp only [w]
    rw [← map_mul,sourceFiniteKP2ProjectiveLift_weyl_square,map_one]
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw₂
  have hn : n = N₀ (0,single₀ x) := sourceKPAdelicLocalProjective_upper K hζ P x
  calc
    _ = w*(r*n*r⁻¹)*w⁻¹ := by rw [← hn,hw,mul_inv_rev]; simp only [mul_assoc]
    _ = w*n*w := by rw [hc.eq.symm,mul_inv_cancel_right,hwi]
    _ = _ := sourceKPAdelicLocalProjective_weyl_upper_weyl K hζ P x

include P in
theorem sourceKPAdelicRootCenter_mem_of_upper_weyl (A : Subgroup G)
    (hN : ∀ x : 𝔸ᶠ[K], N₀ (0,x) ∈ A) (hW : W₀ ∈ A) :
    ∃ z : rootsOfUnity 3 K,
      (sourceKPAdelicCentralComplex K hζ z : ℂ) ≠ 1 ∧
        sourceKPAdelicProjectiveCenter K hζ z ∈ A := by
  have hroot : sourceKPLocalRootSubgroup K hζ P ≤ A.comap ι₀ := by
    apply (Subgroup.closure_le (A.comap ι₀)).mpr
    rintro _ (⟨x,rfl⟩ | ⟨x,rfl⟩)
    · change ι₀ (l₀ (sourceGL2Upper x)) ∈ A
      rw [sourceKPAdelicLocalProjective_upper K hζ P x]
      exact hN _
    · change ι₀ (l₀ (sourceGL2Lower x)) ∈ A
      rw [← sourceKPAdelicRootWeyl_conj_single K hζ P x]
      exact A.mul_mem (A.mul_mem hW (hN _)) (A.inv_mem hW)
  obtain ⟨z,hz,hmem⟩ := sourceKPLocalRootCenter_exists K hζ P
  let e := (sourceKPRootsTransport K hζ P).symm
  refine ⟨e z,?_,?_⟩
  · intro he
    apply hz
    apply e.injective
    apply sourceKPAdelicCentralComplex_injective K hζ
    apply Units.ext
    simpa only [map_one,Units.val_one] using he
  · have h := hroot hmem
    change ι₀ (sourceFiniteKP2ProjectiveCenter K hζ P z) ∈ A at h
    rw [sourceKPAdelicLocalProjective_center K hζ P] at h
    exact h

end
end ArtinMatthews
