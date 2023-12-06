

## Como hacemos lo del splitting?

variable [CommRing K] [Field L] [Field F]
variable (i : K →+* L)

/-- This lemma is for polynomials over a field. -/
theorem splits_iff (f : K[X]) :
    Splits i f ↔ f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 := by
  rw [Splits, map_eq_zero]
#align polynomial.splits_iff Polynomial.splits_iff
/-- This lemma is for polynomials over a field. -/
theorem Splits.def {i : K →+* L} {f : K[X]} (h : Splits i f) :
    f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 :=
  (splits_iff i f).mp h

## Demostrar directamente que F(√n(a)) es galois

Es buena idea usar i : K →+* F para denotar la inclusión de K en F?

## Adjoin solo alpha = √n(a)

F(α) / F es galois <- hay que demostrar esto
- Sabemos que F es ciclotomico
- Sabemos que α ^ n = a ∈ F

De donde sacamos el α?
Podemos demostrar de momento solamente que es primitivo?
Ahh podemos decir que E es el splitting field?

### Otra estrategia...

F S_1 = F S_2
si adjoin F S_1

⊆

####


SF  X^n - a es ciclico
