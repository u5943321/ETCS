val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)
val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)


Definition hom_def:
hom f X Y ⇔ dom f = X ∧ cod f = Y 
End                                                   
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "∶",TM,TOK "→"], 
                  term_name = "hom", paren_style = OnlyIfNecessary}


val _ = new_constant("id", ``:object -> arrow``)                      
val id1 = new_axiom("id1", ``!X. id X ∶ X → X``) 
val _ = export_rewrites["id1"]        
        
val _ = new_constant("compose", ``:arrow -> arrow -> arrow``);
Overload "o" = ``compose``


val idL0 = new_axiom("idL0", ``!X a. cod a = X ==> (id X) o a = a``);

Theorem idL[simp]:
∀f X Y. f∶X→Y ==> (id Y) o f = f
Proof
metis_tac[idL0,hom_def]
QED

val idR0 = new_axiom("idR0", ``!X a. dom a = X ==> a o (id X) = a``);

Theorem idR[simp]:
∀f X Y. f∶X→Y ==> f o (id X) = f
Proof
rw[idR0,hom_def]          
QED

val compose_hom0 = new_axiom("compose_hom0",
                            ``!f g. cod f = dom g ⇒
                                    dom (g o f) = dom f ∧
                                    cod (g o f) = cod g``);

Theorem compose_hom[simp]:
∀f g A B C. f∶ A → B ∧ g∶ B → C ⇒  g o f∶ A→ C
Proof
rw[compose_hom0,hom_def]
QED
                  
val compose_assoc0 = new_axiom("compose_assoc0",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)

Theorem compose_assoc[simp]:
∀f g h A B C D. f∶A → B ∧ g∶B → C ∧ h∶C→ D ⇒
                (h o g) o f = h o (g o f)
Proof
rw[compose_assoc0,hom_def]
QED


(*ax1 all finite root exists, initial, terminal, prod, coprod, eq, coeq*)

val _ = new_constant("one",“:object”)

val ax1_1 = new_axiom("ax1_1",“∀X. ∃!tx. tx∶ X → one”)    

val _ = new_constant("zero",“:object”)

val ax1_2 = new_axiom("ax1_2",“∀X. ∃!ix. ix∶ zero → X”)


val _ = new_constant("po",“:object -> object -> object”)

val _ = new_constant("pa",“:arrow -> arrow -> arrow”)

val _ = new_constant("p1",“:object -> object -> arrow”)

val _ = new_constant("p2",“:object -> object -> arrow”)            

val ax1_3 = new_axiom("ax1_3",“∀A B. (p1 A B) ∶ (po A B) → A ∧ (p2 A B) ∶ (po A B) → B ∧
                                     ∀X f g. f∶ X → A ∧ g∶ X → B ⇒
                                             ∀fg. (fg∶ X → (po A B) ∧
                                                  (p1 A B) o fg = f ∧ (p2 A B) o fg = g) ⇔
                                                  fg = pa f g”)  



val _ = new_constant("eqo",“:arrow -> arrow -> object”)

val _ = new_constant("eqa",“:arrow -> arrow -> arrow”)

val ax1_5 = new_axiom("ax1_5",
                      “∀A B f g. f∶ A → B ∧ g∶ A → B ⇒
                                 (eqa f g)∶ (eqo f g) → A ∧
                                 f o (eqa f g) = g o eqa f g ∧
                                 ∀X h. f o h = g o h ⇒
                                       ∃!x0. x0∶ X → (eqo f g) ∧
                                             (eqa f g) o x0 = h”)                                                                                                            
(*ax2 exponential*)

val _ = new_constant("exp",“:object -> object -> object”)

val _ = new_constant("ev",“:object -> object -> arrow”)

val _ = new_constant("tp",“:arrow -> arrow”)

  

val ax2 = new_axiom("ax2",
                    “∀A B. (ev A B)∶ (po A (exp A B)) → B ∧
                        ∀X f. f∶ (po A X) → B ⇒
                           (∀h. (h∶ X → (exp A B) ∧
                                (ev A B) o
                                (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                                h = tp f) ”)    

      
(*ax3 NNO*)

val _ = new_constant("N",“:object”)

val _ = new_constant("z",“:arrow”)

val _ = new_constant("s",“:arrow”)    

(*turn it into a tuple?*)        

val ax3 = new_axiom("ax3",
                   “z∶ one → N ∧ s∶ N → N ∧
                   ∀X x0 t. x0∶ one → X ∧ t∶ X → X ⇒
                   ∃!x. x∶ N → X ∧ x o z = x0 ∧ x o s = t o x”)    
      

(*ax4 f ≠ g ⇒ ∃a. a ∈ A ∧ f a ≠ g a*)


(*ax5 if dom f has elements, then ∃g. such that fgf = f*)

(*ax6 every object other than 0 has elements*)


(*ax7 element of a sum is a member of one of the injection*)


(*ax8 there exists an object with more than one element*)                                          
