open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____17 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____17 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____26
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____43 = lid_as_data_fv l  in FStar_Syntax_Syntax.fv_to_tm uu____43
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____52 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____52
  
let (fstar_tactics_Failed_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Failed"] 
let (fstar_tactics_Success_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Success"] 
let (fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Failed_lid 
let (fstar_tactics_Success_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Success_lid 
let (fstar_tactics_Failed_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Failed_lid 
let (fstar_tactics_Success_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Success_lid 
let (fstar_tactics_topdown_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TopDown"] 
let (fstar_tactics_bottomup_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "BottomUp"] 
let (fstar_tactics_topdown : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_topdown_lid 
let (fstar_tactics_bottomup : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_bottomup_lid 
let (fstar_tactics_topdown_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_topdown_lid 
let (fstar_tactics_bottomup_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_bottomup_lid 
let (fstar_tactics_Continue_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Continue"] 
let (fstar_tactics_Skip_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Skip"] 
let (fstar_tactics_Abort_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Abort"] 
let (fstar_tactics_Continue : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Continue_lid 
let (fstar_tactics_Skip : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Skip_lid 
let (fstar_tactics_Abort : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Abort_lid 
let (fstar_tactics_Continue_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Continue_lid 
let (fstar_tactics_Skip_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Skip_lid 
let (fstar_tactics_Abort_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Abort_lid 
let (fstar_tactics_SMT_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "SMT"] 
let (fstar_tactics_Goal_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Goal"] 
let (fstar_tactics_Drop_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Drop"] 
let (fstar_tactics_Force_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Force"] 
let (fstar_tactics_SMT : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_SMT_lid 
let (fstar_tactics_Goal : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Goal_lid 
let (fstar_tactics_Drop : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Drop_lid 
let (fstar_tactics_Force : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Force_lid 
let (fstar_tactics_SMT_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_SMT_lid 
let (fstar_tactics_Goal_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Goal_lid 
let (fstar_tactics_Drop_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Drop_lid 
let (fstar_tactics_Force_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Force_lid 
let (fstar_tactics_TacticFailure_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TacticFailure"] 
let (fstar_tactics_EExn_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "EExn"] 
let (fstar_tactics_TacticFailure_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_TacticFailure_lid 
let (fstar_tactics_EExn_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_EExn_lid 
let (fstar_tactics_TacticFailure_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_TacticFailure_lid 
let (fstar_tactics_EExn_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_EExn_lid 
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____162 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____162 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____169 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____169 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____176 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____176 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____183 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____183 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____197 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____197 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____211 =
      let uu____222 = FStar_Syntax_Syntax.as_arg t  in [uu____222]  in
    FStar_Syntax_Util.mk_app t_result uu____211
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____248 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____248 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____255 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____255 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____262 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____262 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____269 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____269 
let (t_ctrl_flag : FStar_Syntax_Syntax.term) =
  let uu____276 = fstar_tactics_lid' ["Types"; "ctrl_flag"]  in
  FStar_Syntax_Syntax.tconst uu____276 
let (fv_ctrl_flag : FStar_Syntax_Syntax.fv) =
  let uu____283 = fstar_tactics_lid' ["Types"; "ctrl_flag"]  in
  FStar_Syntax_Syntax.fvconst uu____283 
let mk_emb :
  'a .
    (FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em  ->
    fun un  ->
      fun t  ->
        let uu____342 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____342
  
let embed :
  'Auu____369 .
    'Auu____369 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____369 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____389 = FStar_Syntax_Embeddings.embed e x  in
        uu____389 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____407 .
    Prims.bool ->
      'Auu____407 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____407 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____431 = FStar_Syntax_Embeddings.unembed e x  in
        uu____431 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____459 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____459 with
    | (hd1,args) ->
        let uu____516 =
          let uu____517 = FStar_Syntax_Util.un_uinst hd1  in
          uu____517.FStar_Syntax_Syntax.n  in
        (uu____516, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____561 =
      let uu____562 = FStar_Syntax_Subst.compress t  in
      uu____562.FStar_Syntax_Syntax.n  in
    match uu____561 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____568;
          FStar_Syntax_Syntax.rng = uu____569;_}
        ->
        let uu____572 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _575  -> FStar_Pervasives_Native.Some _575)
          uu____572
    | uu____576 ->
        (if w
         then
           (let uu____579 =
              let uu____585 =
                let uu____587 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s\n"
                  uu____587
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____585)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____579)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_proofstate unembed_proofstate t_proofstate 
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv  ->
    let uu____678 =
      let uu____686 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____686, [])  in
    FStar_Syntax_Syntax.ET_app uu____678
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____706 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____706;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Thunk.mk
        (fun uu____711  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((proofstate.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)  in
  let unembed_proofstate _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
           FStar_Syntax_Syntax.ltyp = uu____744;
           FStar_Syntax_Syntax.rng = uu____745;_},uu____746)
        ->
        let uu____765 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _768  -> FStar_Pervasives_Native.Some _768)
          uu____765
    | uu____769 ->
        ((let uu____771 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____771
          then
            let uu____795 =
              let uu____801 =
                let uu____803 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu____803
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____801)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____795
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____809 = mkFV fv_proofstate [] []  in
  let uu____814 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____809;
    FStar_TypeChecker_NBETerm.emb_typ = uu____814
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____846 =
      let uu____847 = FStar_Syntax_Subst.compress t  in
      uu____847.FStar_Syntax_Syntax.n  in
    match uu____846 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____853;
          FStar_Syntax_Syntax.rng = uu____854;_}
        ->
        let uu____857 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _860  -> FStar_Pervasives_Native.Some _860)
          uu____857
    | uu____861 ->
        (if w
         then
           (let uu____864 =
              let uu____870 =
                let uu____872 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____872  in
              (FStar_Errors.Warning_NotEmbedded, uu____870)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____864)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_goal unembed_goal t_goal 
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((goal)))" 
let (e_goal_nbe :
  FStar_Tactics_Types.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu____900 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____900;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Thunk.mk
        (fun uu____905  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((goal.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)  in
  let unembed_goal _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
           FStar_Syntax_Syntax.ltyp = uu____938;
           FStar_Syntax_Syntax.rng = uu____939;_},uu____940)
        ->
        let uu____959 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _962  -> FStar_Pervasives_Native.Some _962)
          uu____959
    | uu____963 ->
        ((let uu____965 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____965
          then
            let uu____989 =
              let uu____995 =
                let uu____997 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu____997
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____995)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____989
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____1003 = mkFV fv_goal [] []  in
  let uu____1008 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____1003;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1008
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____1034 uu____1035 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1039 =
          let uu____1040 =
            let uu____1049 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1049  in
          [uu____1040]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
          uu____1039 rng
    | FStar_Tactics_Types.EExn t ->
        let uu___119_1068 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___119_1068.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___119_1068.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____1072 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____1072  in
        let uu____1075 =
          let uu____1076 =
            let uu____1085 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1085  in
          [uu____1076]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
          uu____1075 rng
     in
  let unembed_exn t w uu____1122 =
    let uu____1127 = hd'_and_args t  in
    match uu____1127 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1146)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1181 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1181
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1190 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1205 =
    let uu____1206 =
      let uu____1214 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1214, [])  in
    FStar_Syntax_Syntax.ET_app uu____1206  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1221  -> "(exn)") uu____1205
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1239 =
          let uu____1246 =
            let uu____1251 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1251  in
          [uu____1246]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____1239
    | uu____1261 ->
        let uu____1262 =
          let uu____1264 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1264  in
        failwith uu____1262
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1283,(s,uu____1285)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid
        ->
        let uu____1304 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1304
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1313 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1315 = mkFV fv_exn [] []  in
  let uu____1320 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1315;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1320
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1362 uu____1363 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1369 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1370 =
            let uu____1371 =
              let uu____1380 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1380  in
            let uu____1381 =
              let uu____1392 =
                let uu____1401 = embed ea rng a  in
                FStar_Syntax_Syntax.as_arg uu____1401  in
              let uu____1402 =
                let uu____1413 =
                  let uu____1422 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1422  in
                [uu____1413]  in
              uu____1392 :: uu____1402  in
            uu____1371 :: uu____1381  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1369 uu____1370 rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1457 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1458 =
            let uu____1459 =
              let uu____1468 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1468  in
            let uu____1469 =
              let uu____1480 =
                let uu____1489 = embed e_exn rng e  in
                FStar_Syntax_Syntax.as_arg uu____1489  in
              let uu____1490 =
                let uu____1501 =
                  let uu____1510 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1510  in
                [uu____1501]  in
              uu____1480 :: uu____1490  in
            uu____1459 :: uu____1469  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1457 uu____1458 rng
       in
    let unembed_result t w uu____1564 =
      let uu____1571 = hd'_and_args t  in
      match uu____1571 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____1593)::(ps,uu____1595)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1662 = unembed' w ea a  in
          FStar_Util.bind_opt uu____1662
            (fun a1  ->
               let uu____1670 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1670
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1682)::(ps,uu____1684)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1751 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1751
            (fun e1  ->
               let uu____1759 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1759
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1768 ->
          (if w
           then
             (let uu____1785 =
                let uu____1791 =
                  let uu____1793 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1793
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1791)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1785)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1801 =
      let uu____1802 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1802  in
    let uu____1803 =
      let uu____1804 =
        let uu____1812 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1815 =
          let uu____1818 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1818]  in
        (uu____1812, uu____1815)  in
      FStar_Syntax_Syntax.ET_app uu____1804  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1801 (fun uu____1825  -> "") uu____1803
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1865 =
            let uu____1872 =
              let uu____1877 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1877  in
            let uu____1878 =
              let uu____1885 =
                let uu____1890 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1890  in
              let uu____1891 =
                let uu____1898 =
                  let uu____1903 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1903  in
                [uu____1898]  in
              uu____1885 :: uu____1891  in
            uu____1872 :: uu____1878  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1865
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1922 =
            let uu____1929 =
              let uu____1934 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1934  in
            let uu____1935 =
              let uu____1942 =
                let uu____1947 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1947  in
              let uu____1948 =
                let uu____1955 =
                  let uu____1960 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1960  in
                [uu____1955]  in
              uu____1942 :: uu____1948  in
            uu____1929 :: uu____1935  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1922
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1997,(ps,uu____1999)::(a,uu____2001)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____2033 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____2033
            (fun a1  ->
               let uu____2041 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2041
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2051,(ps,uu____2053)::(e,uu____2055)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____2087 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____2087
            (fun e1  ->
               let uu____2095 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2095
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____2104 -> FStar_Pervasives_Native.None  in
    let uu____2107 = mkFV fv_result [] []  in
    let uu____2112 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____2107;
      FStar_TypeChecker_NBETerm.emb_typ = uu____2112
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____2146 =
      let uu____2147 = FStar_Syntax_Subst.compress t  in
      uu____2147.FStar_Syntax_Syntax.n  in
    match uu____2146 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2154 ->
        (if w
         then
           (let uu____2157 =
              let uu____2163 =
                let uu____2165 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2165
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2163)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2157)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_direction unembed_direction t_direction 
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStar_Tactics_Types.TopDown  ->
        mkConstruct fstar_tactics_topdown_fv [] []
    | FStar_Tactics_Types.BottomUp  ->
        mkConstruct fstar_tactics_bottomup_fv [] []
     in
  let unembed_direction cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2209,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2225,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2240 ->
        ((let uu____2242 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2242
          then
            let uu____2266 =
              let uu____2272 =
                let uu____2274 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2274
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2272)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2266
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2280 = mkFV fv_direction [] []  in
  let uu____2285 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2280;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2285
  } 
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue  -> fstar_tactics_Continue
    | FStar_Tactics_Types.Skip  -> fstar_tactics_Skip
    | FStar_Tactics_Types.Abort  -> fstar_tactics_Abort  in
  let unembed_ctrl_flag w t =
    let uu____2317 =
      let uu____2318 = FStar_Syntax_Subst.compress t  in
      uu____2318.FStar_Syntax_Syntax.n  in
    match uu____2317 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2326 ->
        (if w
         then
           (let uu____2329 =
              let uu____2335 =
                let uu____2337 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2337
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2335)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2329)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_ctrl_flag unembed_ctrl_flag t_ctrl_flag 
let (e_ctrl_flag_nbe :
  FStar_Tactics_Types.ctrl_flag FStar_TypeChecker_NBETerm.embedding) =
  let embed_ctrl_flag cb res =
    match res with
    | FStar_Tactics_Types.Continue  ->
        mkConstruct fstar_tactics_Continue_fv [] []
    | FStar_Tactics_Types.Skip  -> mkConstruct fstar_tactics_Skip_fv [] []
    | FStar_Tactics_Types.Abort  -> mkConstruct fstar_tactics_Abort_fv [] []
     in
  let unembed_ctrl_flag cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2385,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2401,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2417,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2432 ->
        ((let uu____2434 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2434
          then
            let uu____2458 =
              let uu____2464 =
                let uu____2466 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2466
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2464)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2458
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2472 = mkFV fv_ctrl_flag [] []  in
  let uu____2477 = fv_as_emb_typ fv_ctrl_flag  in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu____2472;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2477
  } 
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____2509 =
      let uu____2510 = FStar_Syntax_Subst.compress t  in
      uu____2510.FStar_Syntax_Syntax.n  in
    match uu____2509 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2519 ->
        (if w
         then
           (let uu____2522 =
              let uu____2528 =
                let uu____2530 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2530
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2528)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2522)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_guard_policy unembed_guard_policy t_guard_policy 
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStar_Tactics_Types.SMT  -> mkConstruct fstar_tactics_SMT_fv [] []
    | FStar_Tactics_Types.Goal  -> mkConstruct fstar_tactics_Goal_fv [] []
    | FStar_Tactics_Types.Force  -> mkConstruct fstar_tactics_Force_fv [] []
    | FStar_Tactics_Types.Drop  -> mkConstruct fstar_tactics_Drop_fv [] []
     in
  let unembed_guard_policy cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2584,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2600,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2616,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2632,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2647 -> FStar_Pervasives_Native.None  in
  let uu____2648 = mkFV fv_guard_policy [] []  in
  let uu____2653 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2648;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2653
  } 