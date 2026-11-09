module

public import ArtinMatthews.SourceReflectionLocalFactors
public import ArtinMatthews.SourceReflectionExteriorSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The three exterior factors, with independent row and column masks. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "q" => sourceReflectionPrimeNorm K S₀
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ
local notation "F" => sourceReflectionSphericalFixedPhase K S₀ hζ
local notation "A" => sourceReflectionActiveFixedPhase K S₀ hζ
local notation "j" => sourceReflectionDigitIndex K S₀
local notation "R" => fun P : Pr => sourceReflectionTameRotatedActive K hζ S₀ P hS

def sourceReflectionExteriorInactiveFactor (P : Pr) : ℂ :=
  1 - (Ideal.absNorm P.val.asIdeal : ℂ)⁻¹

def sourceReflectionExteriorFrozenPrime (ε : U) (h : E) (f : Finset Pr)
    (a n : E) (P : Pr) : ℂ :=
  R P (j h P) (a P) 1 * (↑(A ε f a n P ^ sourceReflectionTameActiveExponent (j h P) (a P)) : ℂ)

def sourceReflectionExteriorRowPrime (ε : U) (f : Finset Pr) (a n d : E) (P : Pr) : ℂ :=
  R P 1 0 1 * (↑(A ε f a n P * D P d ^ (-2 : ℤ)) : ℂ)

def sourceReflectionExteriorRowActivePhase (h a d : E) (P : Pr) : ℂ :=
  (↑((D P d ^ (-2 : ℤ)) ^ sourceReflectionTameActiveExponent (j h P) (a P)) : ℂ)

def sourceReflectionExteriorColumnActivePhase (h a c : E) (P : Pr) : ℂ :=
  (↑(D P c ^ sourceReflectionTameActiveExponent (j h P) (a P)) : ℂ)

def sourceReflectionExteriorColumnPrime (ε : U) (f : Finset Pr) (a : E) (P : Pr) : ℂ :=
  (↑(F ε f a P ^ (2 : ℕ)) : ℂ)

def sourceReflectionExteriorFrozen (ε : U) (h : E) (f : Finset Pr) (a n : E) : ℂ :=
  (∏ P ∈ h.support \ f, sourceReflectionExteriorInactiveFactor K S₀ P) *
    ∏ P ∈ f, sourceReflectionExteriorFrozenPrime K S₀ hζ hS ε h f a n P

def sourceReflectionExteriorRow (ε : U) (h : E) (f : Finset Pr) (a n d : E) : ℂ :=
  if SourceReflectionExteriorRowSupport K S₀ h n d then
    (∏ P ∈ d.support, sourceReflectionExteriorRowPrime K S₀ hζ hS ε f a n d P) *
      ∏ P ∈ f, sourceReflectionExteriorRowActivePhase K S₀ hζ h a d P
  else 0

def sourceReflectionExteriorColumn (ε : U) (h : E) (f : Finset Pr) (a c : E) : ℂ :=
  if SourceReflectionExteriorColumnSupport K S₀ f c then
    (∏ P ∈ f, sourceReflectionExteriorColumnActivePhase K S₀ hζ h a c P) *
      (∏ P ∈ c.support, sourceReflectionExteriorColumnPrime K S₀ hζ ε f a P) *
      reflectionGammaTwo K hζ S₀ c
  else 0

/-- The entire separated coefficient before the retained (S)-local character. -/
def sourceReflectionExteriorSeparated (ε : U) (h : E) (f : Finset Pr) (a n d c : E) : ℂ :=
  sourceReflectionExteriorFrozen K S₀ hζ hS ε h f a n *
    sourceReflectionExteriorRow K S₀ hζ hS ε h f a n d *
    sourceReflectionExteriorColumn K S₀ hζ ε h f a c *
    sourceReflectionQuadraticSymbol K S₀ hζ d c /
      ((Real.sqrt (sourcePrimeExponentNorm K S₀ c : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ))

theorem sourceReflectionExteriorSeparated_zero_of_overlap (ε : U) (h : E) (f : Finset Pr)
    (a n d c : E) (hdc : ¬ Disjoint d.support c.support) :
    sourceReflectionExteriorSeparated K S₀ hζ hS ε h f a n d c = 0 := by
  rw [sourceReflectionExteriorSeparated,
    sourceReflectionQuadraticSymbol_eq_zero_of_not_disjoint K S₀ hζ d c hdc, mul_zero, zero_div]

theorem sourceReflectionExteriorRow_eq_zero_of_not_support (ε : U) (h : E) (f : Finset Pr)
    (a n d : E) (hd : ¬ SourceReflectionExteriorRowSupport K S₀ h n d) :
    sourceReflectionExteriorRow K S₀ hζ hS ε h f a n d = 0 :=
  ite_eq_right hd

theorem sourceReflectionExteriorColumn_eq_zero_of_not_support (ε : U) (h : E) (f : Finset Pr)
    (a c : E) (hc : ¬ SourceReflectionExteriorColumnSupport K S₀ f c) :
    sourceReflectionExteriorColumn K S₀ hζ ε h f a c = 0 :=
  ite_eq_right hc

end
end ArtinMatthews.SourceEulerAssembly
