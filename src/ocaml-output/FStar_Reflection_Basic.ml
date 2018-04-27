open Prims
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____6) ->
        FStar_Reflection_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Q_Explicit
  
let (pack_aqual : FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.aqual)
  =
  fun aqv  ->
    match aqv with
    | FStar_Reflection_Data.Q_Explicit  -> FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____21 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____21
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let attr =
      let uu____35 = FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid
         in
      if uu____35
      then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
      else
        (let uu____39 = FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid
            in
         if uu____39
         then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         else
           (let uu____43 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
            if uu____43
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
            else
              (let uu____47 =
                 FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
               if uu____47
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
               else FStar_Pervasives_Native.None)))
       in
    let uu____51 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____51
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "999"))
      attr
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____68::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____96 = init xs  in x :: uu____96
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____105) ->
        let uu____118 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____118
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____120) ->
        FStar_Reflection_Data.C_String s
    | uu____121 ->
        let uu____122 =
          let uu____123 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____123  in
        failwith uu____122
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____132) -> inspect_ln t3
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____181 = last args  in
        (match uu____181 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____201 =
               let uu____206 =
                 let uu____207 =
                   let uu____212 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____212  in
                 uu____207 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____206, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____201)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____221,uu____222) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t3,k) ->
        let body =
          match bs with
          | [] -> t3
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t3, k))
                FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
           in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____295 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____311 ->
        let uu____324 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____324 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        FStar_Reflection_Data.Tv_Refine (bv, t3)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____348 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____348
    | FStar_Syntax_Syntax.Tm_uvar ctx_u ->
        let uu____350 =
          let uu____359 =
            let uu____360 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____360  in
          (uu____359, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
            (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
            (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
           in
        FStar_Reflection_Data.Tv_Uvar uu____350
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____378 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____397 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____448 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____448
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____467 =
                let uu____474 =
                  FStar_List.map
                    (fun uu____486  ->
                       match uu____486 with
                       | (p1,uu____494) -> inspect_pat p1) ps
                   in
                (fv, uu____474)  in
              FStar_Reflection_Data.Pat_Cons uu____467
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
           in
        let brs1 =
          FStar_List.map
            (fun uu___58_543  ->
               match uu___58_543 with
               | (pat,uu____565,t4) ->
                   let uu____583 = inspect_pat pat  in (uu____583, t4)) brs
           in
        FStar_Reflection_Data.Tv_Match (t3, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____588 ->
        ((let uu____590 =
            let uu____595 =
              let uu____596 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____597 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n" uu____596
                uu____597
               in
            (FStar_Errors.Warning_CantInspect, uu____595)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____590);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____604) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____616 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____616
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____618)::(post,uu____620)::uu____621 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____650 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____660 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____660
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___59_666  ->
                    match uu___59_666 with
                    | FStar_Syntax_Syntax.DECREASES uu____667 -> true
                    | uu____670 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____681 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____689 -> FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____704) ->
        FStar_Syntax_Syntax.mk_Total t
    | uu____709 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____716 =
          let uu____727 = FStar_BigInt.string_of_big_int i  in
          (uu____727, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____716
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack_ln : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv -> FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_BVar bv -> FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = pack_aqual q  in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) -> FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____788 =
          let uu____795 =
            let uu____796 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____796  in
          FStar_Syntax_Syntax.mk uu____795  in
        uu____788 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____804 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____804 (g, bs, t)
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((true, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____868 =
                let uu____869 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____869  in
              FStar_All.pipe_left wrap uu____868
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____876 =
                let uu____877 =
                  let uu____890 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____906 = pack_pat p1  in (uu____906, false))
                      ps
                     in
                  (fv, uu____890)  in
                FStar_Syntax_Syntax.Pat_cons uu____877  in
              FStar_All.pipe_left wrap uu____876
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___60_952  ->
               match uu___60_952 with
               | (pat,t1) ->
                   let uu____969 = pack_pat pat  in
                   (uu____969, FStar_Pervasives_Native.None, t1)) brs
           in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs1))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inl t), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inr c), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv x y  in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in x t 
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      let uu____1122 = FStar_TypeChecker_Env.lookup_qname env lid  in
      match uu____1122 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____1143,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____1247) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____1256 -> failwith "global Sig_let has bv"  in
        FStar_Reflection_Data.Sg_Let
          (r, fv, (lb.FStar_Syntax_Syntax.lbtyp),
            (lb.FStar_Syntax_Syntax.lbdef))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,t,uu____1261,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____1272 =
          let uu____1285 = FStar_List.map FStar_Ident.path_of_lid c_lids  in
          (nm, bs, t, uu____1285)  in
        FStar_Reflection_Data.Sg_Inductive uu____1272
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,t,uu____1295,n1,uu____1297) ->
        let uu____1302 =
          let uu____1307 = FStar_Ident.path_of_lid lid  in (uu____1307, t)
           in
        FStar_Reflection_Data.Sg_Constructor uu____1302
    | uu____1308 -> FStar_Reflection_Data.Unk
  
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv  ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,def) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) [] ty
            FStar_Parser_Const.effect_Tot_lid def []
            def.FStar_Syntax_Syntax.pos
           in
        let uu____1321 =
          let uu____1322 =
            let uu____1329 =
              let uu____1332 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____1332]  in
            ((r, [lb]), uu____1329)  in
          FStar_Syntax_Syntax.Sig_let uu____1322  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____1321
    | FStar_Reflection_Data.Sg_Constructor uu____1337 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____1342 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____1360 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____1361 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____1360;
      FStar_Reflection_Data.bv_index = uu____1361;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____1367 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____1368 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____1367;
      FStar_Syntax_Syntax.index = uu____1368;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2)
  =
  fun b  ->
    let uu____1382 = b  in
    match uu____1382 with
    | (bv,aq) -> let uu____1389 = inspect_aqual aq  in (bv, uu____1389)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  -> fun aqv  -> let uu____1400 = pack_aqual aqv  in (bv, uu____1400) 
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____1425 = FStar_Syntax_Util.un_uinst t1  in
      let uu____1426 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____1425 uu____1426
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 