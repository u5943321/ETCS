





Theorem Thm3:
∀A B f h. f∶ A → B ∧
          h∶ (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                    ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A)))) →
             (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) ∧
          (eqa ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
               ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) o h o
          (coeqa (p1 A A o (eqa (f o p1 A A) (f o p2 A A)))
                 (p2 A A o (eqa (f o p1 A A) (f o p2 A A))))  = f ⇒
          is_iso h
Proof
rw[] >>
qabbrev_tac ‘I' = (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                  ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A))))’ >>
qabbrev_tac ‘I0 = (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B)))’ >>      qabbrev_tac ‘k = eqa (f o p1 A A) (f o p2 A A)’ >>
qabbrev_tac ‘k' = coeqa (i1 B B o f) (i2 B B o f)’ >>
qabbrev_tac ‘q = coeqa (p1 A A o k) (p2 A A o k)’ >>
qabbrev_tac ‘q' = eqa (k' o i1 B B) (k' o i2 B B)’ >>
qabbrev_tac ‘R = eqo (f o (p1 A A)) (f o (p2 A A))’ >>
qabbrev_tac ‘R' = coeqo ((i1 B B) o f) ((i2 B B) o f)’ >>
‘k∶ R → (A× A)’ by cheat >>
‘q∶ A → I'’ by cheat >>
‘q'∶ I0 → B’ by cheat >>
‘k'∶ (B + B) → R'’ by cheat >>
irule mono_epi_is_iso >> strip_tac (* 2 *)
>- cheat (*symmetry so called, fix later*)
>- ‘is_mono (q' o h)’ suffices_by cheat (*o_mono_mono*) >>
   Cases_on ‘A ≅ zero’ (* 2 *)
   >- (*lemma*) cheat
   >- ‘∃t. t∶ I' → A ∧ q o t = id I'’ by cheat (*epi_non_zero_pre_inv*)>>
      ‘f o t = q o h’ by cheat >>
      irule is_mono_applied >>
      ‘q' o h∶ I' → B’ by metis_tac[compose_hom] >>
      qexistsl_tac [‘I'’,‘B’] >> simp[] >> rpt strip_tac >>
      rename [‘(q' ∘ h) ∘ u = (q' ∘ h) ∘ u'’] >>
      ‘∃w. w∶ X → R ∧ k o w = ⟨t o u, t o u'⟩’
        by
         (‘f o (p1 A A) o ⟨t o u, t o u'⟩ =
           f o (p2 A A) o ⟨t o u, t o u'⟩’
           by
            (‘f o (p1 A A) o ⟨t o u, t o u'⟩ =
              f o t o u’ by cheat >>
             ‘f o t o u = q o h o u’ by cheat >>
             ‘q o h o u = q o h o u'’ by cheat >>
             ‘q o h o u' = f o t o u'’ by cheat >>
             ‘f o t o u' = f o (p2 A A) o ⟨t o u, t o u'⟩’
               by cheat >>
             metis_tac[]) >>
          qexists_tac
          ‘eq_induce (f ∘ p1 A A) (f ∘ p2 A A) ⟨t ∘ u,t ∘ u'⟩’ >>
          ‘(f ∘ p1 A A) ∘ ⟨t ∘ u,t ∘ u'⟩ = (f ∘ p2 A A) ∘ ⟨t ∘ u,t ∘ u'⟩’
            by cheat >>
          ‘(f ∘ p1 A A)∶ (A× A) → B’ by metis_tac[compose_hom,p1_hom] >>
          ‘(f ∘ p2 A A)∶ (A× A) → B’ by metis_tac[compose_hom,p2_hom] >>
          ‘⟨t ∘ u,t ∘ u'⟩∶ X → (A×A)’ by cheat >>
          strip_tac (*2 *)
          >- (simp[Abbr‘R’] >> metis_tac[ax1_5_applied])
          >- (simp[Abbr‘k’] >> metis_tac[eq_fac])
         ) >>
       ‘u = q o t o u’ by cheat >>
       ‘t o u = (p1 A A) o ⟨t o u, t o u'⟩’ by cheat >> 
       (*need add hom to assumption later*)
       ‘q o t o u = q o (p1 A A) o ⟨t o u, t o u'⟩’ by metis_tac[] >>
       ‘q o (p1 A A) o ⟨t o u, t o u'⟩ = q o p1 A A o k o w’
         by cheat >>
       ‘q o (p1 A A) o k = q o (p2 A A) o k’ by cheat >>
       (*lemma for coeq*)
       ‘q o p1 A A o k o w =  q o (p2 A A) o k o w’ by cheat >>
       ‘q o (p2 A A) o k o w = q o (p2 A A) o ⟨t o u, t o u'⟩’
         by metis_tac[] >>
       ‘ q o (p2 A A) o ⟨t o u, t o u'⟩ = q o t o u'’ by cheat >>
       ‘q o t o u' = u'’ by cheat >>
       metis_tac[]
   

Theorem Thm3_without_assume_exists:

Proof
