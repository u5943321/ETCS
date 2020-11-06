structure ETCSaxiomTheory :> ETCSaxiomTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading ETCSaxiomTheory ... "
    else ()
  
  open Type Term Thm
  local open indexedListsTheory patternMatchesTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "ETCSaxiom"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/ETCS/ETCSaxiomTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op id1 _ = () val op id1 = TDB.find "id1"
  fun op idL0 _ = () val op idL0 = TDB.find "idL0"
  fun op idR0 _ = () val op idR0 = TDB.find "idR0"
  fun op compose_hom0 _ = () val op compose_hom0 = TDB.find "compose_hom0"
  fun op compose_assoc0 _ = ()
  val op compose_assoc0 = TDB.find "compose_assoc0"
  fun op ax1_1 _ = () val op ax1_1 = TDB.find "ax1_1"
  fun op ax1_2 _ = () val op ax1_2 = TDB.find "ax1_2"
  fun op ax1_3 _ = () val op ax1_3 = TDB.find "ax1_3"
  fun op ax1_4 _ = () val op ax1_4 = TDB.find "ax1_4"
  fun op ax1_5 _ = () val op ax1_5 = TDB.find "ax1_5"
  fun op ax1_6 _ = () val op ax1_6 = TDB.find "ax1_6"
  fun op ax2 _ = () val op ax2 = TDB.find "ax2"
  fun op ax3 _ = () val op ax3 = TDB.find "ax3"
  fun op ax4 _ = () val op ax4 = TDB.find "ax4"
  fun op ax5 _ = () val op ax5 = TDB.find "ax5"
  fun op ax6 _ = () val op ax6 = TDB.find "ax6"
  fun op ax7 _ = () val op ax7 = TDB.find "ax7"
  fun op ax8 _ = () val op ax8 = TDB.find "ax8"
  fun op hom_def _ = () val op hom_def = TDB.find "hom_def"
  fun op is_iso_def _ = () val op is_iso_def = TDB.find "is_iso_def"
  fun op are_iso_def _ = () val op are_iso_def = TDB.find "are_iso_def"
  fun op is_mono_def _ = () val op is_mono_def = TDB.find "is_mono_def"
  fun op is_subset_def _ = ()
  val op is_subset_def = TDB.find "is_subset_def"
  fun op is_mem_def _ = () val op is_mem_def = TDB.find "is_mem_def"
  fun op idL _ = () val op idL = TDB.find "idL"
  fun op idR _ = () val op idR = TDB.find "idR"
  fun op compose_hom _ = () val op compose_hom = TDB.find "compose_hom"
  fun op compose_assoc _ = ()
  val op compose_assoc = TDB.find "compose_assoc"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ETCSaxiom_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ETCSaxiom"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ETCSaxiom_grammars = 
    Portable.## (addtyUDs,addtmUDs) ETCSaxiom_grammars
  val _ = Parse.grammarDB_insert("ETCSaxiom",ETCSaxiom_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "ETCSaxiom"

end
