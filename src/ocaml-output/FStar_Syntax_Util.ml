open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____26 = FStar_ST.op_Bang tts_f  in
    match uu____26 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____90 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____90 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____97 =
      let uu____100 =
        let uu____103 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____103]  in
      FStar_List.append lid.FStar_Ident.ns uu____100  in
    FStar_Ident.lid_of_ids uu____97
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        Prims.int_zero
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____121 .
    (FStar_Syntax_Syntax.bv * 'Auu____121) ->
      (FStar_Syntax_Syntax.term * 'Auu____121)
  =
  fun uu____134  ->
    match uu____134 with
    | (b,imp) ->
        let uu____141 = FStar_Syntax_Syntax.bv_to_name b  in (uu____141, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____193 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____193
            then []
            else (let uu____212 = arg_of_non_null_binder b  in [uu____212])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____247 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____329 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____329
              then
                let b1 =
                  let uu____355 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____355, (FStar_Pervasives_Native.snd b))  in
                let uu____362 = arg_of_non_null_binder b1  in (b1, uu____362)
              else
                (let uu____385 = arg_of_non_null_binder b  in (b, uu____385))))
       in
    FStar_All.pipe_right uu____247 FStar_List.unzip
  
let (name_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____519 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____519
              then
                let uu____528 = b  in
                match uu____528 with
                | (a,imp) ->
                    let b1 =
                      let uu____548 =
                        let uu____550 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____550  in
                      FStar_Ident.id_of_text uu____548  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = Prims.int_zero;
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____595 =
          let uu____596 =
            let uu____611 = name_binders binders  in (uu____611, comp)  in
          FStar_Syntax_Syntax.Tm_arrow uu____596  in
        FStar_Syntax_Syntax.mk uu____595 t.FStar_Syntax_Syntax.pos
    | uu____630 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____667  ->
            match uu____667 with
            | (t,imp) ->
                let uu____678 =
                  let uu____679 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____679
                   in
                (uu____678, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____734  ->
            match uu____734 with
            | (t,imp) ->
                let uu____751 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____751, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____764 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____764
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____776 . 'Auu____776 -> 'Auu____776 Prims.list =
  fun s  -> [s] 
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals  ->
    fun actuals  ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f  ->
             fun a  ->
               fun out  ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
  
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____902  ->
             fun uu____903  ->
               match (uu____902, uu____903) with
               | ((x,uu____929),(y,uu____931)) ->
                   let uu____952 =
                     let uu____959 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____959)  in
                   FStar_Syntax_Syntax.NT uu____952) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____975) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____981,uu____982) -> unmeta e2
    | uu____1023 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1037 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1044 -> e1
         | uu____1053 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1055,uu____1056) ->
        unmeta_safe e2
    | uu____1097 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1116 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1119 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1133 = univ_kernel u1  in
        (match uu____1133 with | (k,n1) -> (k, (n1 + Prims.int_one)))
    | FStar_Syntax_Syntax.U_max uu____1150 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1159 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1174 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1174
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1194,uu____1195) ->
          failwith "Impossible: compare_univs"
      | (uu____1199,FStar_Syntax_Syntax.U_bvar uu____1200) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_unknown ,uu____1205) -> ~- Prims.int_one
      | (uu____1207,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_zero ,uu____1210) -> ~- Prims.int_one
      | (uu____1212,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____1216,FStar_Syntax_Syntax.U_unif
         uu____1217) -> ~- Prims.int_one
      | (FStar_Syntax_Syntax.U_unif uu____1227,FStar_Syntax_Syntax.U_name
         uu____1228) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1256 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1258 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1256 - uu____1258
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1276 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1276
                 (fun uu____1292  ->
                    match uu____1292 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> Prims.int_zero
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.int_zero
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1320,uu____1321) -> ~- Prims.int_one
      | (uu____1325,FStar_Syntax_Syntax.U_max uu____1326) -> Prims.int_one
      | uu____1330 ->
          let uu____1335 = univ_kernel u1  in
          (match uu____1335 with
           | (k1,n1) ->
               let uu____1346 = univ_kernel u2  in
               (match uu____1346 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = Prims.int_zero then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1377 = compare_univs u1 u2  in uu____1377 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1396 =
        let uu____1397 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1397;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1396
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1417 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1426 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1449 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1458 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1485 =
          let uu____1486 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1486  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1485;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1515 =
          let uu____1516 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1516  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1515;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___225_1552 = c  in
      let uu____1553 =
        let uu____1554 =
          let uu___227_1555 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___227_1555.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___227_1555.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___227_1555.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___227_1555.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1554  in
      {
        FStar_Syntax_Syntax.n = uu____1553;
        FStar_Syntax_Syntax.pos = (uu___225_1552.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___225_1552.FStar_Syntax_Syntax.vars)
      }
  
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____1595 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1617)::[] -> wp
      | uu____1642 ->
          let uu____1653 =
            let uu____1655 =
              let uu____1657 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1657 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1655
             in
          failwith uu____1653
       in
    let uu____1681 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1681, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1695 -> true
    | FStar_Syntax_Syntax.GTotal uu____1705 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1730  ->
               match uu___0_1730 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1734 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1751  ->
            match uu___1_1751 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1755 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1787 -> true
    | FStar_Syntax_Syntax.GTotal uu____1797 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1812  ->
                   match uu___2_1812 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1815 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  -> (is_pure_effect l) || (is_ghost_effect l) 
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1856 =
      let uu____1857 = FStar_Syntax_Subst.compress t  in
      uu____1857.FStar_Syntax_Syntax.n  in
    match uu____1856 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1861,c) -> is_pure_or_ghost_comp c
    | uu____1883 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1898 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1907 =
      let uu____1908 = FStar_Syntax_Subst.compress t  in
      uu____1908.FStar_Syntax_Syntax.n  in
    match uu____1907 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1912,c) -> is_lemma_comp c
    | uu____1934 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1942 =
      let uu____1943 = FStar_Syntax_Subst.compress t  in
      uu____1943.FStar_Syntax_Syntax.n  in
    match uu____1942 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1947) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1973) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2010,t1,uu____2012) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2038,uu____2039) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2081) -> head_of t1
    | uu____2086 -> t
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____2164 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____2246 = head_and_args' head1  in
        (match uu____2246 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2315 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2342) ->
        FStar_Syntax_Subst.compress t2
    | uu____2347 -> t1
  
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___3_2365  ->
                   match uu___3_2365 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2368 -> false)))
    | uu____2370 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2387) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2397) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2426 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2435 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___366_2447 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___366_2447.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___366_2447.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___366_2447.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___366_2447.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2463  ->
            match uu___4_2463 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2467 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2475 -> []
    | FStar_Syntax_Syntax.GTotal uu____2492 -> []
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.effect_args
  
let (primops : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.op_Eq;
  FStar_Parser_Const.op_notEq;
  FStar_Parser_Const.op_LT;
  FStar_Parser_Const.op_LTE;
  FStar_Parser_Const.op_GT;
  FStar_Parser_Const.op_GTE;
  FStar_Parser_Const.op_Subtraction;
  FStar_Parser_Const.op_Minus;
  FStar_Parser_Const.op_Addition;
  FStar_Parser_Const.op_Multiply;
  FStar_Parser_Const.op_Division;
  FStar_Parser_Const.op_Modulus;
  FStar_Parser_Const.op_And;
  FStar_Parser_Const.op_Or;
  FStar_Parser_Const.op_Negation] 
let (is_primop_lid : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____2536 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2546,uu____2547) ->
        unascribe e2
    | uu____2588 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
      FStar_Util.either * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2641,uu____2642) ->
          ascribe t' k
      | uu____2683 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2710 =
      let uu____2719 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2719  in
    uu____2710 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2775 =
      let uu____2776 = FStar_Syntax_Subst.compress t  in
      uu____2776.FStar_Syntax_Syntax.n  in
    match uu____2775 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2780 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2780
    | uu____2781 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2788 =
      let uu____2789 = FStar_Syntax_Subst.compress t  in
      uu____2789.FStar_Syntax_Syntax.n  in
    match uu____2788 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2793 ->
             let uu____2802 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2802
         | uu____2803 -> t)
    | uu____2804 -> t
  
let (eq_lazy_kind :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazy_kind -> Prims.bool)
  =
  fun k  ->
    fun k'  ->
      match (k, k') with
      | (FStar_Syntax_Syntax.BadLazy ,FStar_Syntax_Syntax.BadLazy ) -> true
      | (FStar_Syntax_Syntax.Lazy_bv ,FStar_Syntax_Syntax.Lazy_bv ) -> true
      | (FStar_Syntax_Syntax.Lazy_binder ,FStar_Syntax_Syntax.Lazy_binder )
          -> true
      | (FStar_Syntax_Syntax.Lazy_optionstate
         ,FStar_Syntax_Syntax.Lazy_optionstate ) -> true
      | (FStar_Syntax_Syntax.Lazy_fvar ,FStar_Syntax_Syntax.Lazy_fvar ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_comp ,FStar_Syntax_Syntax.Lazy_comp ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_env ,FStar_Syntax_Syntax.Lazy_env ) -> true
      | (FStar_Syntax_Syntax.Lazy_proofstate
         ,FStar_Syntax_Syntax.Lazy_proofstate ) -> true
      | (FStar_Syntax_Syntax.Lazy_goal ,FStar_Syntax_Syntax.Lazy_goal ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt ,FStar_Syntax_Syntax.Lazy_sigelt )
          -> true
      | (FStar_Syntax_Syntax.Lazy_uvar ,FStar_Syntax_Syntax.Lazy_uvar ) ->
          true
      | uu____2829 -> false
  
let unlazy_as_t :
  'Auu____2842 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2842
  =
  fun k  ->
    fun t  ->
      let uu____2853 =
        let uu____2854 = FStar_Syntax_Subst.compress t  in
        uu____2854.FStar_Syntax_Syntax.n  in
      match uu____2853 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2859;
            FStar_Syntax_Syntax.rng = uu____2860;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2863 -> failwith "Not a Tm_lazy of the expected kind"
  
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun typ  ->
      fun k  ->
        fun r  ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange  in
          let i =
            let uu____2904 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2904;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i) rng
  
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2915 =
      let uu____2930 = unascribe t  in head_and_args' uu____2930  in
    match uu____2915 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2962 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2973 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2984 -> false
  
let (injectives : Prims.string Prims.list) =
  ["FStar.Int8.int_to_t";
  "FStar.Int16.int_to_t";
  "FStar.Int32.int_to_t";
  "FStar.Int64.int_to_t";
  "FStar.UInt8.uint_to_t";
  "FStar.UInt16.uint_to_t";
  "FStar.UInt32.uint_to_t";
  "FStar.UInt64.uint_to_t";
  "FStar.Int8.__int_to_t";
  "FStar.Int16.__int_to_t";
  "FStar.Int32.__int_to_t";
  "FStar.Int64.__int_to_t";
  "FStar.UInt8.__uint_to_t";
  "FStar.UInt16.__uint_to_t";
  "FStar.UInt32.__uint_to_t";
  "FStar.UInt64.__uint_to_t"] 
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f  ->
    fun g  ->
      match (f, g) with
      | (Equal ,Equal ) -> Equal
      | (NotEqual ,uu____3034) -> NotEqual
      | (uu____3035,NotEqual ) -> NotEqual
      | (Unknown ,uu____3036) -> Unknown
      | (uu____3037,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3142 = if uu___5_3142 then Equal else Unknown  in
      let equal_iff uu___6_3153 = if uu___6_3153 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3174 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3196 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3196
        then
          let uu____3200 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3277  ->
                    match uu____3277 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3318 = eq_tm a1 a2  in
                        eq_inj acc uu____3318) Equal) uu____3200
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3332 =
          let uu____3349 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3349 head_and_args  in
        match uu____3332 with
        | (head1,args1) ->
            let uu____3402 =
              let uu____3419 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3419 head_and_args  in
            (match uu____3402 with
             | (head2,args2) ->
                 let uu____3472 =
                   let uu____3477 =
                     let uu____3478 = un_uinst head1  in
                     uu____3478.FStar_Syntax_Syntax.n  in
                   let uu____3481 =
                     let uu____3482 = un_uinst head2  in
                     uu____3482.FStar_Syntax_Syntax.n  in
                   (uu____3477, uu____3481)  in
                 (match uu____3472 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     f,FStar_Syntax_Syntax.Tm_fvar g) when
                      (f.FStar_Syntax_Syntax.fv_qual =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Data_ctor))
                        &&
                        (g.FStar_Syntax_Syntax.fv_qual =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Data_ctor))
                      -> FStar_Pervasives_Native.Some (f, args1, g, args2)
                  | uu____3509 -> FStar_Pervasives_Native.None))
         in
      let uu____3522 =
        let uu____3527 =
          let uu____3528 = unmeta t11  in uu____3528.FStar_Syntax_Syntax.n
           in
        let uu____3531 =
          let uu____3532 = unmeta t21  in uu____3532.FStar_Syntax_Syntax.n
           in
        (uu____3527, uu____3531)  in
      match uu____3522 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3538,uu____3539) ->
          let uu____3540 = unlazy t11  in eq_tm uu____3540 t21
      | (uu____3541,FStar_Syntax_Syntax.Tm_lazy uu____3542) ->
          let uu____3543 = unlazy t21  in eq_tm t11 uu____3543
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3546 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3570 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3570
            (fun uu____3618  ->
               match uu____3618 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3633 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3633
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3647 = eq_tm f g  in
          eq_and uu____3647
            (fun uu____3650  ->
               let uu____3651 = eq_univs_list us vs  in equal_if uu____3651)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3653),uu____3654) -> Unknown
      | (uu____3655,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3656)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3659 = FStar_Const.eq_const c d  in equal_iff uu____3659
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3662)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3664))) ->
          let uu____3693 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3693
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3747 =
            let uu____3752 =
              let uu____3753 = un_uinst h1  in
              uu____3753.FStar_Syntax_Syntax.n  in
            let uu____3756 =
              let uu____3757 = un_uinst h2  in
              uu____3757.FStar_Syntax_Syntax.n  in
            (uu____3752, uu____3756)  in
          (match uu____3747 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3763 =
                    let uu____3765 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3765  in
                  FStar_List.mem uu____3763 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3767 ->
               let uu____3772 = eq_tm h1 h2  in
               eq_and uu____3772 (fun uu____3774  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3880 = FStar_List.zip bs1 bs2  in
            let uu____3943 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3980  ->
                 fun a  ->
                   match uu____3980 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4073  -> branch_matches b1 b2))
              uu____3880 uu____3943
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4078 = eq_univs u v1  in equal_if uu____4078
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4092 = eq_quoteinfo q1 q2  in
          eq_and uu____4092 (fun uu____4094  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4107 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4107 (fun uu____4109  -> eq_tm phi1 phi2)
      | uu____4110 -> Unknown

and (eq_quoteinfo :
  FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.quoteinfo -> eq_result)
  =
  fun q1  ->
    fun q2  ->
      if q1.FStar_Syntax_Syntax.qkind <> q2.FStar_Syntax_Syntax.qkind
      then NotEqual
      else
        eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes
          q2.FStar_Syntax_Syntax.antiquotes

and (eq_antiquotes :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) Prims.list -> eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ([],uu____4182) -> NotEqual
      | (uu____4213,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4305 = eq_tm t1 t2  in
             match uu____4305 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4306 = eq_antiquotes a11 a21  in
                 (match uu____4306 with
                  | NotEqual  -> NotEqual
                  | uu____4307 -> Unknown)
             | Equal  -> eq_antiquotes a11 a21)

and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> eq_result)
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____4391,uu____4392) -> false  in
      let uu____4402 = b1  in
      match uu____4402 with
      | (p1,w1,t1) ->
          let uu____4436 = b2  in
          (match uu____4436 with
           | (p2,w2,t2) ->
               let uu____4470 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4470
               then
                 let uu____4473 =
                   (let uu____4477 = eq_tm t1 t2  in uu____4477 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4486 = eq_tm t11 t21  in
                             uu____4486 = Equal) w1 w2)
                    in
                 (if uu____4473 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4551)::a11,(b,uu____4554)::b1) ->
          let uu____4628 = eq_tm a b  in
          (match uu____4628 with
           | Equal  -> eq_args a11 b1
           | uu____4629 -> Unknown)
      | uu____4630 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Equal
      | (FStar_Pervasives_Native.None ,uu____4685) -> NotEqual
      | (uu____4692,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4722 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4739) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4745,uu____4746) ->
        unrefine t2
    | uu____4787 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4795 =
      let uu____4796 = FStar_Syntax_Subst.compress t  in
      uu____4796.FStar_Syntax_Syntax.n  in
    match uu____4795 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4800 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4815) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4820 ->
        let uu____4837 =
          let uu____4838 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4838 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4837 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4901,uu____4902) ->
        is_uvar t1
    | uu____4943 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4952 =
      let uu____4953 = unrefine t  in uu____4953.FStar_Syntax_Syntax.n  in
    match uu____4952 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4959) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4985) -> is_unit t1
    | uu____4990 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4999 =
      let uu____5000 = FStar_Syntax_Subst.compress t  in
      uu____5000.FStar_Syntax_Syntax.n  in
    match uu____4999 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5005 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5014 =
      let uu____5015 = FStar_Syntax_Subst.compress e  in
      uu____5015.FStar_Syntax_Syntax.n  in
    match uu____5014 with
    | FStar_Syntax_Syntax.Tm_abs uu____5019 -> true
    | uu____5039 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5048 =
      let uu____5049 = FStar_Syntax_Subst.compress t  in
      uu____5049.FStar_Syntax_Syntax.n  in
    match uu____5048 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5053 -> true
    | uu____5069 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5079) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5085,uu____5086) ->
        pre_typ t2
    | uu____5127 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____5152 =
        let uu____5153 = un_uinst typ1  in uu____5153.FStar_Syntax_Syntax.n
         in
      match uu____5152 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5218 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5248 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5269,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5276) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5281,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5292,uu____5293,uu____5294,uu____5295,uu____5296) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5306,uu____5307,uu____5308,uu____5309) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5315,uu____5316,uu____5317,uu____5318,uu____5319) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5327,uu____5328) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5330,uu____5331) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5333 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5334 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5335 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5336 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5349 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5373 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5399  ->
    match uu___7_5399 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5413 'Auu____5414 .
    ('Auu____5413 FStar_Syntax_Syntax.syntax * 'Auu____5414) ->
      FStar_Range.range
  =
  fun uu____5425  ->
    match uu____5425 with | (hd1,uu____5433) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5447 'Auu____5448 .
    ('Auu____5447 FStar_Syntax_Syntax.syntax * 'Auu____5448) Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
  
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____5546 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) r
  
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun bs  ->
      let uu____5605 =
        FStar_List.map
          (fun uu____5632  ->
             match uu____5632 with
             | (bv,aq) ->
                 let uu____5651 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5651, aq)) bs
         in
      mk_app f uu____5605
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.op_Hat field_projector_prefix
        (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let itext = i.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText itext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5722 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5722
          then
            let uu____5725 =
              let uu____5731 =
                let uu____5733 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5733  in
              let uu____5736 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5731, uu____5736)  in
            FStar_Ident.mk_ident uu____5725
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5751) -> ses
    | uu____5760 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5775 = FStar_Syntax_Unionfind.find uv  in
      match uu____5775 with
      | FStar_Pervasives_Native.Some uu____5778 ->
          let uu____5779 =
            let uu____5781 =
              let uu____5783 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5783  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5781  in
          failwith uu____5779
      | uu____5788 -> FStar_Syntax_Unionfind.change uv t
  
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1  ->
    fun q2  ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator
         l1,FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector
         (l1a,l1b),FStar_Syntax_Syntax.Projector (l2a,l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | uu____5871 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____5917 =
                let uu___994_5918 = rc  in
                let uu____5919 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___994_5918.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5919;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___994_5918.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5917
           in
        match bs with
        | [] -> t
        | uu____5936 ->
            let body =
              let uu____5938 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____5938  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____5968 =
                   let uu____5969 =
                     let uu____5988 =
                       let uu____5997 = FStar_Syntax_Subst.close_binders bs
                          in
                       FStar_List.append uu____5997 bs'  in
                     let uu____6012 = close_lopt lopt'  in
                     (uu____5988, t1, uu____6012)  in
                   FStar_Syntax_Syntax.Tm_abs uu____5969  in
                 FStar_Syntax_Syntax.mk uu____5968 t1.FStar_Syntax_Syntax.pos
             | uu____6027 ->
                 let uu____6028 =
                   let uu____6029 =
                     let uu____6048 = FStar_Syntax_Subst.close_binders bs  in
                     let uu____6057 = close_lopt lopt  in
                     (uu____6048, body, uu____6057)  in
                   FStar_Syntax_Syntax.Tm_abs uu____6029  in
                 FStar_Syntax_Syntax.mk uu____6028 t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____6113 ->
          let uu____6122 =
            let uu____6123 =
              let uu____6138 = FStar_Syntax_Subst.close_binders bs  in
              let uu____6147 = FStar_Syntax_Subst.close_comp bs c  in
              (uu____6138, uu____6147)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6123  in
          FStar_Syntax_Syntax.mk uu____6122 c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6196 =
        let uu____6197 = FStar_Syntax_Subst.compress t  in
        uu____6197.FStar_Syntax_Syntax.n  in
      match uu____6196 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6227) ->
               let uu____6236 =
                 let uu____6237 = FStar_Syntax_Subst.compress tres  in
                 uu____6237.FStar_Syntax_Syntax.n  in
               (match uu____6236 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu____6280 -> t)
           | uu____6281 -> t)
      | uu____6282 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6300 =
        let uu____6301 =
          let uu____6308 =
            let uu____6311 =
              let uu____6312 = FStar_Syntax_Syntax.mk_binder b  in
              [uu____6312]  in
            FStar_Syntax_Subst.close uu____6311 t  in
          (b, uu____6308)  in
        FStar_Syntax_Syntax.Tm_refine uu____6301  in
      let uu____6333 =
        let uu____6334 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6334 t.FStar_Syntax_Syntax.pos  in
      FStar_Syntax_Syntax.mk uu____6300 uu____6333
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6394 = is_total_comp c  in
        if uu____6394
        then
          let uu____6409 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6409 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6476;
           FStar_Syntax_Syntax.index = uu____6477;
           FStar_Syntax_Syntax.sort = s;_},uu____6479)
        ->
        let rec aux s1 k2 =
          let uu____6510 =
            let uu____6511 = FStar_Syntax_Subst.compress s1  in
            uu____6511.FStar_Syntax_Syntax.n  in
          match uu____6510 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6526 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6541;
                 FStar_Syntax_Syntax.index = uu____6542;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6544)
              -> aux s2 k2
          | uu____6552 ->
              let uu____6553 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6553)
           in
        aux s k1
    | uu____6568 ->
        let uu____6569 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6569)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6594 = arrow_formals_comp_ln k  in
    match uu____6594 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6649 = arrow_formals_comp_ln k  in
    match uu____6649 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6716 = arrow_formals_comp k  in
    match uu____6716 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6818 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6818 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6842 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6851  ->
                         match uu___8_6851 with
                         | FStar_Syntax_Syntax.DECREASES uu____6853 -> true
                         | uu____6857 -> false))
                  in
               (match uu____6842 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6892 ->
                    let uu____6895 = is_total_comp c1  in
                    if uu____6895
                    then
                      let uu____6914 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____6914 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7007;
             FStar_Syntax_Syntax.index = uu____7008;
             FStar_Syntax_Syntax.sort = k2;_},uu____7010)
          -> arrow_until_decreases k2
      | uu____7018 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7039 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7039 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7093 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7114 =
                 FStar_Common.tabulate n_univs (fun uu____7120  -> false)  in
               let uu____7123 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7148  ->
                         match uu____7148 with
                         | (x,uu____7157) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7114 uu____7123)
           in
        ((n_univs + (FStar_List.length bs)), uu____7093)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7213 =
            let uu___1121_7214 = rc  in
            let uu____7215 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1121_7214.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7215;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1121_7214.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7213
      | uu____7224 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7258 =
        let uu____7259 =
          let uu____7262 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7262  in
        uu____7259.FStar_Syntax_Syntax.n  in
      match uu____7258 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7308 = aux t2 what  in
          (match uu____7308 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7380 -> ([], t1, abs_body_lcomp)  in
    let uu____7397 = aux t FStar_Pervasives_Native.None  in
    match uu____7397 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7445 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7445 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7479 =
      match uu____7479 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7493 -> aq  in
          (b, aq1)
       in
    let uu____7498 = arrow_formals_comp_ln t  in
    match uu____7498 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7535 ->
             let uu____7544 =
               let uu____7545 =
                 let uu____7560 = FStar_List.map no_acc bs  in
                 (uu____7560, c)  in
               FStar_Syntax_Syntax.Tm_arrow uu____7545  in
             FStar_Syntax_Syntax.mk uu____7544 t.FStar_Syntax_Syntax.pos)
  
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              fun pos  ->
                {
                  FStar_Syntax_Syntax.lbname = lbname;
                  FStar_Syntax_Syntax.lbunivs = univ_vars;
                  FStar_Syntax_Syntax.lbtyp = typ;
                  FStar_Syntax_Syntax.lbeff = eff;
                  FStar_Syntax_Syntax.lbdef = def;
                  FStar_Syntax_Syntax.lbattrs = lbattrs;
                  FStar_Syntax_Syntax.lbpos = pos
                }
  
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                fun pos  ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None ,uu____7731) -> def
                    | (uu____7742,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7754) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7770  ->
                                  FStar_Syntax_Syntax.U_name _7770))
                           in
                        let inst1 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst1 def
                     in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ
                     in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1  in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
  
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____7852 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7852 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7887 ->
            let t' = arrow binders c  in
            let uu____7899 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7899 with
             | (uvs1,t'1) ->
                 let uu____7920 =
                   let uu____7921 = FStar_Syntax_Subst.compress t'1  in
                   uu____7921.FStar_Syntax_Syntax.n  in
                 (match uu____7920 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7970 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____7995 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8006 -> false
  
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid 
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid 
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid 
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v 
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8069 =
        let uu____8070 = pre_typ t  in uu____8070.FStar_Syntax_Syntax.n  in
      match uu____8069 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8075 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8089 =
        let uu____8090 = pre_typ t  in uu____8090.FStar_Syntax_Syntax.n  in
      match uu____8089 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8094 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8096) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8122) ->
          is_constructed_typ t1 lid
      | uu____8127 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8140 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8141 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8142 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8144) -> get_tycon t2
    | uu____8169 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8177 =
      let uu____8178 = un_uinst t  in uu____8178.FStar_Syntax_Syntax.n  in
    match uu____8177 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8183 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8197 =
        let uu____8201 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8201  in
      match uu____8197 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8233 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Range.dummyRange
  
let (type_u :
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu____8252  ->
    let u =
      let uu____8258 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8275  -> FStar_Syntax_Syntax.U_unif _8275)
        uu____8258
       in
    let uu____8276 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange
       in
    (uu____8276, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8289 = eq_tm a a'  in
      match uu____8289 with | Equal  -> true | uu____8292 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8297 =
    let uu____8298 =
      let uu____8299 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange
         in
      FStar_Syntax_Syntax.lid_as_fv uu____8299
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Syntax.Tm_fvar uu____8298  in
  FStar_Syntax_Syntax.mk uu____8297 FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Range.dummyRange
  
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Range.dummyRange
  
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Range.dummyRange
  
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Range.dummyRange
  
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
    FStar_Pervasives_Native.None
  
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid 
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr 
let (tcdecltime_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.tcdecltime_attr 
let (inline_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.inline_let_attr 
let (rename_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.rename_let_attr 
let (t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid 
let (mk_conj_opt :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____8412 =
            let uu____8415 =
              let uu____8416 =
                let uu____8433 =
                  let uu____8444 = FStar_Syntax_Syntax.as_arg phi11  in
                  let uu____8453 =
                    let uu____8464 = FStar_Syntax_Syntax.as_arg phi2  in
                    [uu____8464]  in
                  uu____8444 :: uu____8453  in
                (tand, uu____8433)  in
              FStar_Syntax_Syntax.Tm_app uu____8416  in
            let uu____8509 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            FStar_Syntax_Syntax.mk uu____8415 uu____8509  in
          FStar_Pervasives_Native.Some uu____8412
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8542 =
          let uu____8543 =
            let uu____8560 =
              let uu____8571 = FStar_Syntax_Syntax.as_arg phi1  in
              let uu____8580 =
                let uu____8591 = FStar_Syntax_Syntax.as_arg phi2  in
                [uu____8591]  in
              uu____8571 :: uu____8580  in
            (op_t, uu____8560)  in
          FStar_Syntax_Syntax.Tm_app uu____8543  in
        let uu____8636 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Syntax.mk uu____8542 uu____8636
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8649 =
      let uu____8650 =
        let uu____8667 =
          let uu____8678 = FStar_Syntax_Syntax.as_arg phi  in [uu____8678]
           in
        (t_not, uu____8667)  in
      FStar_Syntax_Syntax.Tm_app uu____8650  in
    FStar_Syntax_Syntax.mk uu____8649 phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____8875 =
      let uu____8876 =
        let uu____8893 =
          let uu____8904 = FStar_Syntax_Syntax.as_arg e  in [uu____8904]  in
        (b2t_v, uu____8893)  in
      FStar_Syntax_Syntax.Tm_app uu____8876  in
    FStar_Syntax_Syntax.mk uu____8875 e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8951 = head_and_args e  in
    match uu____8951 with
    | (hd1,args) ->
        let uu____8996 =
          let uu____9011 =
            let uu____9012 = FStar_Syntax_Subst.compress hd1  in
            uu____9012.FStar_Syntax_Syntax.n  in
          (uu____9011, args)  in
        (match uu____8996 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9029)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9064 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9086 =
      let uu____9087 = unmeta t  in uu____9087.FStar_Syntax_Syntax.n  in
    match uu____9086 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9092 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9115 = is_t_true t1  in
      if uu____9115
      then t2
      else
        (let uu____9122 = is_t_true t2  in
         if uu____9122 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9150 = is_t_true t1  in
      if uu____9150
      then t_true
      else
        (let uu____9157 = is_t_true t2  in
         if uu____9157 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9186 =
        let uu____9187 =
          let uu____9204 =
            let uu____9215 = FStar_Syntax_Syntax.as_arg e1  in
            let uu____9224 =
              let uu____9235 = FStar_Syntax_Syntax.as_arg e2  in [uu____9235]
               in
            uu____9215 :: uu____9224  in
          (teq, uu____9204)  in
        FStar_Syntax_Syntax.Tm_app uu____9187  in
      let uu____9280 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      FStar_Syntax_Syntax.mk uu____9186 uu____9280
  
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____9303 =
            let uu____9304 =
              let uu____9321 =
                let uu____9332 = FStar_Syntax_Syntax.iarg t  in
                let uu____9341 =
                  let uu____9352 = FStar_Syntax_Syntax.as_arg e1  in
                  let uu____9361 =
                    let uu____9372 = FStar_Syntax_Syntax.as_arg e2  in
                    [uu____9372]  in
                  uu____9352 :: uu____9361  in
                uu____9332 :: uu____9341  in
              (eq_inst, uu____9321)  in
            FStar_Syntax_Syntax.Tm_app uu____9304  in
          let uu____9425 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          FStar_Syntax_Syntax.mk uu____9303 uu____9425
  
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun x  ->
      fun t'  ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid  in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Range.dummyRange
           in
        let uu____9450 =
          let uu____9451 =
            let uu____9468 =
              let uu____9479 = FStar_Syntax_Syntax.iarg t  in
              let uu____9488 =
                let uu____9499 = FStar_Syntax_Syntax.as_arg x  in
                let uu____9508 =
                  let uu____9519 = FStar_Syntax_Syntax.as_arg t'  in
                  [uu____9519]  in
                uu____9499 :: uu____9508  in
              uu____9479 :: uu____9488  in
            (t_has_type1, uu____9468)  in
          FStar_Syntax_Syntax.Tm_app uu____9451  in
        FStar_Syntax_Syntax.mk uu____9450 FStar_Range.dummyRange
  
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun t  ->
      fun e  ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Range.dummyRange
           in
        let uu____9596 =
          let uu____9597 =
            let uu____9614 =
              let uu____9625 = FStar_Syntax_Syntax.iarg t  in
              let uu____9634 =
                let uu____9645 = FStar_Syntax_Syntax.as_arg e  in
                [uu____9645]  in
              uu____9625 :: uu____9634  in
            (t_with_type1, uu____9614)  in
          FStar_Syntax_Syntax.Tm_app uu____9597  in
        FStar_Syntax_Syntax.mk uu____9596 FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9692 =
    let uu____9693 =
      let uu____9700 =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
          FStar_Syntax_Syntax.delta_constant
          (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
         in
      (uu____9700, [FStar_Syntax_Syntax.U_zero])  in
    FStar_Syntax_Syntax.Tm_uinst uu____9693  in
  FStar_Syntax_Syntax.mk uu____9692 FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____9783 =
          let uu____9784 =
            let uu____9801 =
              let uu____9812 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
              let uu____9821 =
                let uu____9832 =
                  let uu____9841 =
                    let uu____9842 =
                      let uu____9843 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____9843]  in
                    abs uu____9842 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0))
                     in
                  FStar_Syntax_Syntax.as_arg uu____9841  in
                [uu____9832]  in
              uu____9812 :: uu____9821  in
            (fa, uu____9801)  in
          FStar_Syntax_Syntax.Tm_app uu____9784  in
        FStar_Syntax_Syntax.mk uu____9783 FStar_Range.dummyRange
  
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let (close_forall_no_univs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____9970 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____9970
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____9989 -> true
    | uu____9991 -> false
  
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____10038 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10038, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10067 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10067, FStar_Pervasives_Native.None, t2)  in
        let uu____10081 =
          let uu____10082 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10082  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu____10081
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None
         in
      let uu____10158 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10161 =
        let uu____10172 = FStar_Syntax_Syntax.as_arg p  in [uu____10172]  in
      mk_app uu____10158 uu____10161
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
          FStar_Pervasives_Native.None
         in
      let uu____10212 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10215 =
        let uu____10226 = FStar_Syntax_Syntax.as_arg p  in [uu____10226]  in
      mk_app uu____10212 uu____10215
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10261 = head_and_args t  in
    match uu____10261 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10310 =
          let uu____10325 =
            let uu____10326 = FStar_Syntax_Subst.compress head3  in
            uu____10326.FStar_Syntax_Syntax.n  in
          (uu____10325, args)  in
        (match uu____10310 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10345)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10411 =
                    let uu____10416 =
                      let uu____10417 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10417]  in
                    FStar_Syntax_Subst.open_term uu____10416 p  in
                  (match uu____10411 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10474 -> failwith "impossible"  in
                       let uu____10482 =
                         let uu____10484 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10484
                          in
                       if uu____10482
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10500 -> FStar_Pervasives_Native.None)
         | uu____10503 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10534 = head_and_args t  in
    match uu____10534 with
    | (head1,args) ->
        let uu____10585 =
          let uu____10600 =
            let uu____10601 = FStar_Syntax_Subst.compress head1  in
            uu____10601.FStar_Syntax_Syntax.n  in
          (uu____10600, args)  in
        (match uu____10585 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10623;
               FStar_Syntax_Syntax.vars = uu____10624;_},u::[]),(t1,uu____10627)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10674 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10709 = head_and_args t  in
    match uu____10709 with
    | (head1,args) ->
        let uu____10760 =
          let uu____10775 =
            let uu____10776 = FStar_Syntax_Subst.compress head1  in
            uu____10776.FStar_Syntax_Syntax.n  in
          (uu____10775, args)  in
        (match uu____10760 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10798;
               FStar_Syntax_Syntax.vars = uu____10799;_},u::[]),(t1,uu____10802)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10849 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10877 =
      let uu____10894 = unmeta t  in head_and_args uu____10894  in
    match uu____10877 with
    | (head1,uu____10897) ->
        let uu____10922 =
          let uu____10923 = un_uinst head1  in
          uu____10923.FStar_Syntax_Syntax.n  in
        (match uu____10922 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.squash_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.auto_squash_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.and_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.not_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.imp_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.iff_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.ite_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.exists_lid))
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.forall_lid))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.true_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.false_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq3_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.b2t_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.haseq_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.precedes_lid)
         | uu____10928 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10948 =
      let uu____10949 = FStar_Syntax_Subst.compress t  in
      uu____10949.FStar_Syntax_Syntax.n  in
    match uu____10948 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11055 =
          let uu____11060 =
            let uu____11061 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11061  in
          (b, uu____11060)  in
        FStar_Pervasives_Native.Some uu____11055
    | uu____11066 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11089 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11089
      (fun uu____11117  ->
         match uu____11117 with
         | (b,c) ->
             let uu____11136 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11136 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11199 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11236 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11236
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11288 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11331 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11372 -> false
  
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x)  in
  [(Prims.int_zero,
     [f FStar_Parser_Const.true_lid; f FStar_Parser_Const.false_lid]);
  ((Prims.of_int (2)),
    [f FStar_Parser_Const.and_lid;
    f FStar_Parser_Const.or_lid;
    f FStar_Parser_Const.imp_lid;
    f FStar_Parser_Const.iff_lid;
    f FStar_Parser_Const.eq2_lid;
    f FStar_Parser_Const.eq3_lid]);
  (Prims.int_one, [f FStar_Parser_Const.not_lid]);
  ((Prims.of_int (3)),
    [f FStar_Parser_Const.ite_lid; f FStar_Parser_Const.eq2_lid]);
  ((Prims.of_int (4)), [f FStar_Parser_Const.eq3_lid])] 
let (destruct_sq_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  [((Prims.of_int (2)),
     [(FStar_Parser_Const.c_and_lid, FStar_Parser_Const.and_lid);
     (FStar_Parser_Const.c_or_lid, FStar_Parser_Const.or_lid);
     (FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid);
     (FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  ((Prims.of_int (3)),
    [(FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid)]);
  ((Prims.of_int (4)),
    [(FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  (Prims.int_zero,
    [(FStar_Parser_Const.c_true_lid, FStar_Parser_Const.true_lid);
    (FStar_Parser_Const.c_false_lid, FStar_Parser_Const.false_lid)])]
  
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11758) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11770) ->
          unmeta_monadic t
      | uu____11783 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____11852 =
        match uu____11852 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____11890  ->
                   match uu____11890 with
                   | (lid,out_lid) ->
                       let uu____11899 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____11899
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____11926 = head_and_args t  in
      match uu____11926 with
      | (hd1,args) ->
          let uu____11971 =
            let uu____11972 = un_uinst hd1  in
            uu____11972.FStar_Syntax_Syntax.n  in
          (match uu____11971 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____11978 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____11987 = un_squash t  in
      FStar_Util.bind_opt uu____11987
        (fun t1  ->
           let uu____12003 = head_and_args' t1  in
           match uu____12003 with
           | (hd1,args) ->
               let uu____12042 =
                 let uu____12043 = un_uinst hd1  in
                 uu____12043.FStar_Syntax_Syntax.n  in
               (match uu____12042 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12049 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12090,pats)) ->
          let uu____12128 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12128)
      | uu____12141 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12208 = head_and_args t1  in
        match uu____12208 with
        | (t2,args) ->
            let uu____12263 = un_uinst t2  in
            let uu____12264 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12305  ->
                      match uu____12305 with
                      | (t3,imp) ->
                          let uu____12324 = unascribe t3  in
                          (uu____12324, imp)))
               in
            (uu____12263, uu____12264)
         in
      let rec aux qopt out t1 =
        let uu____12375 = let uu____12399 = flat t1  in (qopt, uu____12399)
           in
        match uu____12375 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12439;
                 FStar_Syntax_Syntax.vars = uu____12440;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12443);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12444;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12445;_},uu____12446)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12548;
                 FStar_Syntax_Syntax.vars = uu____12549;_},uu____12550::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12553);
                  FStar_Syntax_Syntax.pos = uu____12554;
                  FStar_Syntax_Syntax.vars = uu____12555;_},uu____12556)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12673;
               FStar_Syntax_Syntax.vars = uu____12674;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12677);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12678;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12679;_},uu____12680)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12773 =
              let uu____12777 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12777  in
            aux uu____12773 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12787;
               FStar_Syntax_Syntax.vars = uu____12788;_},uu____12789::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12792);
                FStar_Syntax_Syntax.pos = uu____12793;
                FStar_Syntax_Syntax.vars = uu____12794;_},uu____12795)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12904 =
              let uu____12908 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12908  in
            aux uu____12904 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____12918) ->
            let bs = FStar_List.rev out  in
            let uu____12971 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____12971 with
             | (bs1,t2) ->
                 let uu____12980 = patterns t2  in
                 (match uu____12980 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13030 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13085 = un_squash t  in
      FStar_Util.bind_opt uu____13085
        (fun t1  ->
           let uu____13100 = arrow_one t1  in
           match uu____13100 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13115 =
                 let uu____13117 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13117  in
               if uu____13115
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13127 = comp_to_comp_typ_nouniv c  in
                    uu____13127.FStar_Syntax_Syntax.result_typ  in
                  let uu____13128 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13128
                  then
                    let uu____13135 = patterns q  in
                    match uu____13135 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13198 =
                       let uu____13199 =
                         let uu____13204 =
                           let uu____13205 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13216 =
                             let uu____13227 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13227]  in
                           uu____13205 :: uu____13216  in
                         (FStar_Parser_Const.imp_lid, uu____13204)  in
                       BaseConn uu____13199  in
                     FStar_Pervasives_Native.Some uu____13198))
           | uu____13260 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13268 = un_squash t  in
      FStar_Util.bind_opt uu____13268
        (fun t1  ->
           let uu____13299 = head_and_args' t1  in
           match uu____13299 with
           | (hd1,args) ->
               let uu____13338 =
                 let uu____13353 =
                   let uu____13354 = un_uinst hd1  in
                   uu____13354.FStar_Syntax_Syntax.n  in
                 (uu____13353, args)  in
               (match uu____13338 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13371)::(a2,uu____13373)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13424 =
                      let uu____13425 = FStar_Syntax_Subst.compress a2  in
                      uu____13425.FStar_Syntax_Syntax.n  in
                    (match uu____13424 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13432) ->
                         let uu____13467 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13467 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13520 -> failwith "impossible"  in
                              let uu____13528 = patterns q1  in
                              (match uu____13528 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13589 -> FStar_Pervasives_Native.None)
                | uu____13590 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13613 = destruct_sq_forall phi  in
          (match uu____13613 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13623  -> FStar_Pervasives_Native.Some _13623)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13630 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13636 = destruct_sq_exists phi  in
          (match uu____13636 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13646  -> FStar_Pervasives_Native.Some _13646)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13653 -> f1)
      | uu____13656 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13660 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13660
      (fun uu____13665  ->
         let uu____13666 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13666
           (fun uu____13671  ->
              let uu____13672 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13672
                (fun uu____13677  ->
                   let uu____13678 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13678
                     (fun uu____13683  ->
                        let uu____13684 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13684
                          (fun uu____13688  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13706 =
            let uu____13711 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13711  in
          let uu____13712 =
            let uu____13713 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13713  in
          let uu____13716 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13706 a.FStar_Syntax_Syntax.action_univs uu____13712
            FStar_Parser_Const.effect_Tot_lid uu____13716 [] pos
           in
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_let
               ((false, [lb]), [a.FStar_Syntax_Syntax.action_name]));
          FStar_Syntax_Syntax.sigrng =
            ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.sigquals =
            [FStar_Syntax_Syntax.Visible_default;
            FStar_Syntax_Syntax.Action eff_lid];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = [];
          FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
        }
  
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reify_1 =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        t.FStar_Syntax_Syntax.pos
       in
    let uu____13742 =
      let uu____13743 =
        let uu____13760 =
          let uu____13771 = FStar_Syntax_Syntax.as_arg t  in [uu____13771]
           in
        (reify_1, uu____13760)  in
      FStar_Syntax_Syntax.Tm_app uu____13743  in
    FStar_Syntax_Syntax.mk uu____13742 t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13823 =
        let uu____13824 =
          let uu____13825 = FStar_Ident.lid_of_str "Bogus.Effect"  in
          FStar_Const.Const_reflect uu____13825  in
        FStar_Syntax_Syntax.Tm_constant uu____13824  in
      FStar_Syntax_Syntax.mk uu____13823 t.FStar_Syntax_Syntax.pos  in
    let uu____13827 =
      let uu____13828 =
        let uu____13845 =
          let uu____13856 = FStar_Syntax_Syntax.as_arg t  in [uu____13856]
           in
        (reflect_, uu____13845)  in
      FStar_Syntax_Syntax.Tm_app uu____13828  in
    FStar_Syntax_Syntax.mk uu____13827 t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13900 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13917 = unfold_lazy i  in delta_qualifier uu____13917
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13919 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13920 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13921 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13944 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____13957 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____13958 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____13965 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____13966 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13982) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____13987;
           FStar_Syntax_Syntax.index = uu____13988;
           FStar_Syntax_Syntax.sort = t2;_},uu____13990)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____13999) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14005,uu____14006) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14048) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14073,t2,uu____14075) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14100,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____14139 = delta_qualifier t  in incr_delta_depth uu____14139
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14147 =
      let uu____14148 = FStar_Syntax_Subst.compress t  in
      uu____14148.FStar_Syntax_Syntax.n  in
    match uu____14147 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14153 -> false
  
let rec apply_last :
  'Auu____14162 .
    ('Auu____14162 -> 'Auu____14162) ->
      'Auu____14162 Prims.list -> 'Auu____14162 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14188 = f a  in [uu____14188]
      | x::xs -> let uu____14193 = apply_last f xs  in x :: uu____14193
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))
          p
         in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
  
let (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____14248 =
            let uu____14249 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.Tm_fvar uu____14249  in
          FStar_Syntax_Syntax.mk uu____14248 rng  in
        let cons1 args pos =
          let uu____14261 =
            let uu____14262 = ctor FStar_Parser_Const.cons_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14262
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14261 args pos  in
        let nil args pos =
          let uu____14274 =
            let uu____14275 = ctor FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14275
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14274 args pos  in
        let uu____14276 =
          let uu____14277 =
            let uu____14278 = FStar_Syntax_Syntax.iarg typ  in [uu____14278]
             in
          nil uu____14277 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14312 =
                 let uu____14313 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14322 =
                   let uu____14333 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14342 =
                     let uu____14353 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14353]  in
                   uu____14333 :: uu____14342  in
                 uu____14313 :: uu____14322  in
               cons1 uu____14312 t.FStar_Syntax_Syntax.pos) l uu____14276
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____14462 -> false
  
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Util.either -> ('a,'b) FStar_Util.either -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with
          | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
          | uu____14576 -> false
  
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) -> ('a * 'b) -> ('a * 'b) -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
  
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1,FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | uu____14742 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14780 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14780
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
  
let (fail : Prims.string -> Prims.bool) = fun msg  -> check msg false 
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____14982 = unmeta_safe t1  in canon_app uu____14982
           in
        let t21 = let uu____14986 = unmeta_safe t2  in canon_app uu____14986
           in
        let uu____14989 =
          let uu____14994 =
            let uu____14995 =
              let uu____14998 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____14998  in
            uu____14995.FStar_Syntax_Syntax.n  in
          let uu____14999 =
            let uu____15000 =
              let uu____15003 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15003  in
            uu____15000.FStar_Syntax_Syntax.n  in
          (uu____14994, uu____14999)  in
        match uu____14989 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15005,uu____15006) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15015,FStar_Syntax_Syntax.Tm_uinst uu____15016) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15025,uu____15026) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15043,FStar_Syntax_Syntax.Tm_delayed uu____15044) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15061,uu____15062) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15091,FStar_Syntax_Syntax.Tm_ascribed uu____15092) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15131 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15131
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15136 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15136
        | (FStar_Syntax_Syntax.Tm_type
           uu____15139,FStar_Syntax_Syntax.Tm_type uu____15140) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15198 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15198) &&
              (let uu____15208 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15208)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15257 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15257) &&
              (let uu____15267 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15267)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15284 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15284) &&
              (let uu____15288 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15288)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15345 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15345) &&
              (let uu____15349 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15349)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15438 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15438) &&
              (let uu____15442 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15442)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15459,uu____15460) ->
            let uu____15461 =
              let uu____15463 = unlazy t11  in
              term_eq_dbg dbg uu____15463 t21  in
            check "lazy_l" uu____15461
        | (uu____15465,FStar_Syntax_Syntax.Tm_lazy uu____15466) ->
            let uu____15467 =
              let uu____15469 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15469  in
            check "lazy_r" uu____15467
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15514 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15514))
              &&
              (let uu____15518 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15518)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15522),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15524)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15582 =
               let uu____15584 = eq_quoteinfo qi1 qi2  in uu____15584 = Equal
                in
             check "tm_quoted qi" uu____15582) &&
              (let uu____15587 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15587)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15617 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15617) &&
                   (let uu____15621 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15621)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15640 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15640) &&
                    (let uu____15644 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15644))
                   &&
                   (let uu____15648 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15648)
             | uu____15651 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15657) -> fail "unk"
        | (uu____15659,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15661,uu____15662) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15664,uu____15665) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15667,uu____15668) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15670,uu____15671) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15673,uu____15674) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15676,uu____15677) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15697,uu____15698) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15714,uu____15715) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15723,uu____15724) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15742,uu____15743) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15767,uu____15768) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15783,uu____15784) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15798,uu____15799) ->
            fail "bottom"
        | (uu____15807,FStar_Syntax_Syntax.Tm_bvar uu____15808) ->
            fail "bottom"
        | (uu____15810,FStar_Syntax_Syntax.Tm_name uu____15811) ->
            fail "bottom"
        | (uu____15813,FStar_Syntax_Syntax.Tm_fvar uu____15814) ->
            fail "bottom"
        | (uu____15816,FStar_Syntax_Syntax.Tm_constant uu____15817) ->
            fail "bottom"
        | (uu____15819,FStar_Syntax_Syntax.Tm_type uu____15820) ->
            fail "bottom"
        | (uu____15822,FStar_Syntax_Syntax.Tm_abs uu____15823) ->
            fail "bottom"
        | (uu____15843,FStar_Syntax_Syntax.Tm_arrow uu____15844) ->
            fail "bottom"
        | (uu____15860,FStar_Syntax_Syntax.Tm_refine uu____15861) ->
            fail "bottom"
        | (uu____15869,FStar_Syntax_Syntax.Tm_app uu____15870) ->
            fail "bottom"
        | (uu____15888,FStar_Syntax_Syntax.Tm_match uu____15889) ->
            fail "bottom"
        | (uu____15913,FStar_Syntax_Syntax.Tm_let uu____15914) ->
            fail "bottom"
        | (uu____15929,FStar_Syntax_Syntax.Tm_uvar uu____15930) ->
            fail "bottom"
        | (uu____15944,FStar_Syntax_Syntax.Tm_meta uu____15945) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____15980 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____15980)
          (fun q1  ->
             fun q2  ->
               let uu____15992 =
                 let uu____15994 = eq_aqual q1 q2  in uu____15994 = Equal  in
               check "arg qual" uu____15992) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____16019 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16019)
          (fun q1  ->
             fun q2  ->
               let uu____16031 =
                 let uu____16033 = eq_aqual q1 q2  in uu____16033 = Equal  in
               check "binder qual" uu____16031) b1 b2

and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg  ->
    fun c1  ->
      fun c2  ->
        let c11 = comp_to_comp_typ_nouniv c1  in
        let c21 = comp_to_comp_typ_nouniv c2  in
        ((let uu____16047 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16047) &&
           (let uu____16051 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16051))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflag -> FStar_Syntax_Syntax.cflag -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun dbg  ->
    fun uu____16061  ->
      fun uu____16062  ->
        match (uu____16061, uu____16062) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16189 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16189) &&
               (let uu____16193 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16193))
              &&
              (let uu____16197 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16239 -> false  in
               check "branch when" uu____16197)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16260 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16260) &&
           (let uu____16269 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16269))
          &&
          (let uu____16273 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16273)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16290 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16290 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16344 ->
        let uu____16359 =
          let uu____16361 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16361  in
        Prims.int_one + uu____16359
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16364 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16364
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16368 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16368
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16377 = sizeof t1  in (FStar_List.length us) + uu____16377
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16381) ->
        let uu____16406 = sizeof t1  in
        let uu____16408 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16423  ->
                 match uu____16423 with
                 | (bv,uu____16433) ->
                     let uu____16438 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16438) Prims.int_zero bs
           in
        uu____16406 + uu____16408
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16467 = sizeof hd1  in
        let uu____16469 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16484  ->
                 match uu____16484 with
                 | (arg,uu____16494) ->
                     let uu____16499 = sizeof arg  in acc + uu____16499)
            Prims.int_zero args
           in
        uu____16467 + uu____16469
    | uu____16502 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16516 =
        let uu____16517 = un_uinst t  in uu____16517.FStar_Syntax_Syntax.n
         in
      match uu____16516 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16522 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (get_attribute :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.args FStar_Pervasives_Native.option)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.tryPick
        (fun t  ->
           let uu____16583 = head_and_args t  in
           match uu____16583 with
           | (head1,args) ->
               let uu____16638 =
                 let uu____16639 = FStar_Syntax_Subst.compress head1  in
                 uu____16639.FStar_Syntax_Syntax.n  in
               (match uu____16638 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16665 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16698 = is_fvar attr a  in Prims.op_Negation uu____16698)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 s =
        let uu____16719 = FStar_Options.set_options s  in
        match uu____16719 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.op_Hat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  -> FStar_Options.set_ml_ish ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____16733 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16733 (fun a1  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s -> set_options1 s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.internal_push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s -> set_options1 s))
      | FStar_Syntax_Syntax.RestartSolver  -> ()
      | FStar_Syntax_Syntax.PopOptions  ->
          let uu____16748 = FStar_Options.internal_pop ()  in
          if uu____16748
          then ()
          else
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Cannot #pop-options, stack would become empty") r
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16780 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16799 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16814 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16815 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16816 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16825) ->
        let uu____16850 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____16850 with
         | (bs1,t2) ->
             let uu____16859 =
               FStar_List.collect
                 (fun uu____16871  ->
                    match uu____16871 with
                    | (b,uu____16881) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____16886 = unbound_variables t2  in
             FStar_List.append uu____16859 uu____16886)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____16911 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____16911 with
         | (bs1,c1) ->
             let uu____16920 =
               FStar_List.collect
                 (fun uu____16932  ->
                    match uu____16932 with
                    | (b,uu____16942) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____16947 = unbound_variables_comp c1  in
             FStar_List.append uu____16920 uu____16947)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____16956 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____16956 with
         | (bs,t2) ->
             let uu____16979 =
               FStar_List.collect
                 (fun uu____16991  ->
                    match uu____16991 with
                    | (b1,uu____17001) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17006 = unbound_variables t2  in
             FStar_List.append uu____16979 uu____17006)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17035 =
          FStar_List.collect
            (fun uu____17049  ->
               match uu____17049 with
               | (x,uu____17061) -> unbound_variables x) args
           in
        let uu____17070 = unbound_variables t1  in
        FStar_List.append uu____17035 uu____17070
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17111 = unbound_variables t1  in
        let uu____17114 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17129 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17129 with
                  | (p,wopt,t2) ->
                      let uu____17151 = unbound_variables t2  in
                      let uu____17154 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17151 uu____17154))
           in
        FStar_List.append uu____17111 uu____17114
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17168) ->
        let uu____17209 = unbound_variables t1  in
        let uu____17212 =
          let uu____17215 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17246 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17215 uu____17246  in
        FStar_List.append uu____17209 uu____17212
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17287 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17290 =
          let uu____17293 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17296 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17301 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17303 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17303 with
                 | (uu____17324,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17293 uu____17296  in
        FStar_List.append uu____17287 uu____17290
    | FStar_Syntax_Syntax.Tm_let ((uu____17326,lbs),t1) ->
        let uu____17346 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17346 with
         | (lbs1,t2) ->
             let uu____17361 = unbound_variables t2  in
             let uu____17364 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17371 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17374 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17371 uu____17374) lbs1
                in
             FStar_List.append uu____17361 uu____17364)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17391 = unbound_variables t1  in
        let uu____17394 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17399,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17454  ->
                      match uu____17454 with
                      | (a,uu____17466) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17475,uu____17476,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17482,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17488 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17497 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17498 -> []  in
        FStar_List.append uu____17391 uu____17394

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17505) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17515) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17525 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17528 =
          FStar_List.collect
            (fun uu____17542  ->
               match uu____17542 with
               | (a,uu____17554) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17525 uu____17528

let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun attrs  ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu____17669 = head_and_args h  in
            (match uu____17669 with
             | (head1,args) ->
                 let uu____17730 =
                   let uu____17731 = FStar_Syntax_Subst.compress head1  in
                   uu____17731.FStar_Syntax_Syntax.n  in
                 (match uu____17730 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17784 -> aux (h :: acc) t))
         in
      aux [] attrs
  
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun se  ->
      let uu____17808 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17808 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2476_17850 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2476_17850.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2476_17850.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2476_17850.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2476_17850.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2476_17850.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17858 =
      let uu____17859 = FStar_Syntax_Subst.compress t  in
      uu____17859.FStar_Syntax_Syntax.n  in
    match uu____17858 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____17863,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____17891)::uu____17892 ->
                  let pats' = unmeta pats  in
                  let uu____17952 = head_and_args pats'  in
                  (match uu____17952 with
                   | (head1,uu____17971) ->
                       let uu____17996 =
                         let uu____17997 = un_uinst head1  in
                         uu____17997.FStar_Syntax_Syntax.n  in
                       (match uu____17996 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18002 -> false))
              | uu____18004 -> false)
         | uu____18016 -> false)
    | uu____18018 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18034 =
      let uu____18051 = unmeta e  in head_and_args uu____18051  in
    match uu____18034 with
    | (head1,args) ->
        let uu____18082 =
          let uu____18097 =
            let uu____18098 = un_uinst head1  in
            uu____18098.FStar_Syntax_Syntax.n  in
          (uu____18097, args)  in
        (match uu____18082 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18116) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18140::(hd1,uu____18142)::(tl1,uu____18144)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18211 =
               let uu____18214 =
                 let uu____18217 = list_elements tl1  in
                 FStar_Util.must uu____18217  in
               hd1 :: uu____18214  in
             FStar_Pervasives_Native.Some uu____18211
         | uu____18226 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18255 =
      let uu____18256 = FStar_Syntax_Subst.compress t  in
      uu____18256.FStar_Syntax_Syntax.n  in
    match uu____18255 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18263) ->
        let uu____18298 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18298 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18332 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18332
             then
               let uu____18339 =
                 let uu____18350 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18350]  in
               mk_app t uu____18339
             else e1)
    | uu____18377 ->
        let uu____18378 =
          let uu____18389 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18389]  in
        mk_app t uu____18378
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18444 = list_elements e  in
        match uu____18444 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18479 =
          let uu____18496 = unmeta p  in
          FStar_All.pipe_right uu____18496 head_and_args  in
        match uu____18479 with
        | (head1,args) ->
            let uu____18547 =
              let uu____18562 =
                let uu____18563 = un_uinst head1  in
                uu____18563.FStar_Syntax_Syntax.n  in
              (uu____18562, args)  in
            (match uu____18547 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18585,uu____18586)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18638 ->
                 let uu____18653 =
                   let uu____18659 =
                     let uu____18661 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18661
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18659)  in
                 FStar_Errors.raise_error uu____18653
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18704 =
            let uu____18721 = unmeta t1  in
            FStar_All.pipe_right uu____18721 head_and_args  in
          match uu____18704 with
          | (head1,args) ->
              let uu____18768 =
                let uu____18783 =
                  let uu____18784 = un_uinst head1  in
                  uu____18784.FStar_Syntax_Syntax.n  in
                (uu____18783, args)  in
              (match uu____18768 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18803)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18840 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____18870 = smt_pat_or t1  in
            (match uu____18870 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____18892 = list_elements1 e  in
                 FStar_All.pipe_right uu____18892
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____18922 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____18922
                           (FStar_List.map one_pat)))
             | uu____18951 ->
                 let uu____18956 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____18956])
        | uu____19011 ->
            let uu____19014 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19014]
         in
      let uu____19069 =
        let uu____19102 =
          let uu____19103 = FStar_Syntax_Subst.compress t  in
          uu____19103.FStar_Syntax_Syntax.n  in
        match uu____19102 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19160 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19160 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19231;
                        FStar_Syntax_Syntax.effect_name = uu____19232;
                        FStar_Syntax_Syntax.result_typ = uu____19233;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19235)::(post,uu____19237)::(pats,uu____19239)::[];
                        FStar_Syntax_Syntax.flags = uu____19240;_}
                      ->
                      let uu____19301 = lemma_pats pats  in
                      (binders1, pre, post, uu____19301)
                  | uu____19338 -> failwith "impos"))
        | uu____19372 -> failwith "Impos"  in
      match uu____19069 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19464 =
              let uu____19465 =
                let uu____19472 = mk_imp pre post1  in
                let uu____19475 =
                  let uu____19476 =
                    let uu____19497 =
                      FStar_Syntax_Syntax.binders_to_names binders  in
                    (uu____19497, patterns)  in
                  FStar_Syntax_Syntax.Meta_pattern uu____19476  in
                (uu____19472, uu____19475)  in
              FStar_Syntax_Syntax.Tm_meta uu____19465  in
            FStar_Syntax_Syntax.mk uu____19464 t.FStar_Syntax_Syntax.pos  in
          let quant =
            let uu____19521 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19521 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19551 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19562 -> true
    | uu____19564 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19575 -> true
    | uu____19577 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19595 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19596 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19597 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19598 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19599 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19600 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19601 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19602 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19605 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19608 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19595;
        FStar_Syntax_Syntax.bind_wp = uu____19596;
        FStar_Syntax_Syntax.stronger = uu____19597;
        FStar_Syntax_Syntax.if_then_else = uu____19598;
        FStar_Syntax_Syntax.ite_wp = uu____19599;
        FStar_Syntax_Syntax.close_wp = uu____19600;
        FStar_Syntax_Syntax.trivial = uu____19601;
        FStar_Syntax_Syntax.repr = uu____19602;
        FStar_Syntax_Syntax.return_repr = uu____19605;
        FStar_Syntax_Syntax.bind_repr = uu____19608
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19640 =
        match uu____19640 with
        | (ts1,ts2) ->
            let uu____19651 = f ts1  in
            let uu____19652 = f ts2  in (uu____19651, uu____19652)
         in
      let uu____19653 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19658 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19663 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19668 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19673 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19653;
        FStar_Syntax_Syntax.l_return = uu____19658;
        FStar_Syntax_Syntax.l_bind = uu____19663;
        FStar_Syntax_Syntax.l_subcomp = uu____19668;
        FStar_Syntax_Syntax.l_if_then_else = uu____19673
      }
  
let (apply_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.eff_combinators ->
      FStar_Syntax_Syntax.eff_combinators)
  =
  fun f  ->
    fun combs  ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          let uu____19695 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19695
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19697 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19697
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19699 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19699
  
let (get_wp_close_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | uu____19714 -> FStar_Pervasives_Native.None
  
let (get_eff_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19728 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19728
          (fun _19735  -> FStar_Pervasives_Native.Some _19735)
  
let (get_bind_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
          FStar_Pervasives_Native.snd
  
let (get_return_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
          FStar_Pervasives_Native.snd
  
let (get_bind_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19775 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19775
          (fun _19782  -> FStar_Pervasives_Native.Some _19782)
  
let (get_return_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19796 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19796
          (fun _19803  -> FStar_Pervasives_Native.Some _19803)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19817  -> FStar_Pervasives_Native.Some _19817)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19821  -> FStar_Pervasives_Native.Some _19821)
    | uu____19822 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19834 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19834
          (fun _19841  -> FStar_Pervasives_Native.Some _19841)
    | uu____19842 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19856  -> FStar_Pervasives_Native.Some _19856)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19860  -> FStar_Pervasives_Native.Some _19860)
    | uu____19861 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19875  -> FStar_Pervasives_Native.Some _19875)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19879  -> FStar_Pervasives_Native.Some _19879)
    | uu____19880 -> FStar_Pervasives_Native.None
  
let (get_stronger_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
          FStar_Pervasives_Native.snd
  
let (get_stronger_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff uu____19904 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____19905 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19907 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19907
          (fun _19914  -> FStar_Pervasives_Native.Some _19914)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun _19928  -> FStar_Pervasives_Native.Some _19928)
    | uu____19929 -> FStar_Pervasives_Native.None
  