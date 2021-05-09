#import "Basic";
#import "File";
#import "String";
#import "Random";

main :: () {
  args := get_command_line_arguments();
  if args.count == 1 {
    print("Please supply a *.cnf sat file to the program.\n");
    return;
  }

  file_name := args[1];
  num_vars, formula := parse_sat_file(file_name);
  sat, sat_vars := search(num_vars, formula);
  if sat {
    for clause: formula {
      print_clause(clause);
    }
    for s: sat_vars {
      print("x%=%, ", it_index, s);
    }
    print("sat\n");
  } else {
    print("unsat\n");
  }
}

parse_sat_file :: (file_name: string)-> int, [..]Clause {
  text := read_entire_file(file_name);
  lines := split(text, "\n");
  clauses : [..]Clause;
  num_vars := -1;
  num_clauses   := -1;

  for line : lines {
    tokens := split(line, " ");
    if tokens.count == 0 {
      continue;
    }
    if equal(tokens[0], "c") {
      continue;
    }

    else if equal(tokens[0], "p") {
      num_vars = string_to_int(tokens[2]);
      num_clauses   = string_to_int(tokens[3]);
      array_reserve(*clauses, num_clauses);
    } else {
      clause : Clause;
      for token : tokens {
        val, correct := string_to_int(token);
        if correct == false then continue;
        //assert(correct, "Not parsed correctly, token=%, val=%", tokens, val);
        if val == 0
          break;
        if val < 0 {
          val = -val - 1;
          var : Var = cast(Var) Var.NOT | (cast(Var) val);
          array_add(*clause, var);
        } else {
          val = val - 1;
          var : Var = cast(Var) val;
          array_add(*clause, var);
        }


      }
      array_add(*clauses, clause);
    }
  }

  return num_vars, clauses;
}

// following the minisat pseudo-code
search :: (num_vars: int, formula: [..]Clause) -> bool, Sat_Vars {
  // conflict driven clause learning
  sat_vars := create_sat_vars(num_vars);
  assigns: [..]LogVar;
  learnt_clauses: [..]Clause;
  array_reserve(*assigns, sat_vars.count);
  array_reserve(*learnt_clauses, num_vars / 2);
  lit_priorities, not_priorities := init_priorities_vsids(num_vars, formula);
  heap := init_heap_vsids(num_vars, lit_priorities, not_priorities);

  level := 0;
  while true {
    status := boolean_constant_propagation(*sat_vars, formula, learnt_clauses, *assigns, level);
    if status == Propagation_Status.Conflict {
      b, c := analyze_conflict_last_uip(sat_vars, assigns, level);
      print("b=%\n", b);
      print_clause(c);
      if level < 0 then
        return false, sat_vars;

      level = b;
      array_add(*learnt_clauses, c);
      backtrack(*sat_vars, heap, *assigns, c, lit_priorities, not_priorities, level);
      continue;
    }

    if all_variables_assigned(sat_vars) then
      break;

    level = level + 1;
    decide_vsids(*sat_vars, *assigns, level, heap, lit_priorities, not_priorities);
  }

  return true, sat_vars;
}

backtrack :: (sat_vars: *Sat_Vars, heap: Heap, assigns: *[..]LogVar, clause: Clause, lit: [..]float, not: [..]float, level: int) {
  count := lit.count-1;
  for i: 0..count {
    lit[i] *= 0.5;
    not[i] *= 0.5;
  }
  for var: clause {
    idx, not_flag := get_var_num(var);
    if not {
      not[idx] += 1.0;
    } else {
      lit[idx] += 1.0;
    }
  }
  array_reset(*heap.arr);

  while assigns.count {
    log_var := pop(assigns);
    if log_var.level <= level {
      array_add(assigns, log_var);
      break;
    }
    print("Backtracking level=%, x%=???\n", log_var.level, log_var.var_num);
    unassign_value(sat_vars, log_var.var_num);
  }

  for var, i: sat_vars {
    if var == BoolAssign.Unass {
      enqueue(heap, i, lit, not);
    }
  }
}

decide_vsids :: (sat_vars: *Sat_Vars, assigns: *[..]LogVar, level: int, heap: Heap, lit: [..]float, not: [..]float) #expand {
  while true {
    assert(count(heap)>0);
    val := dequeue(heap, lit, not);
    if value_at(<<sat_vars, val) == BoolAssign.Unass {
      assign_value(sat_vars, val, lit[val]>not[val]);
      print("Decide x%=% @ level=%\n", val, lit[val]>not[val], level);
      array_add(assigns, create_log_var(val, level, -1));
      break;
    }
  }
}

decide_rand :: (sat_vars: *Sat_Vars, assigns: *[..]LogVar, level: int) #expand {
  while true {
    r := random_get() % sat_vars.count;
    bool_assign := value_at(<<sat_vars, r);
    if bool_assign == BoolAssign.Unass {
      b := cast(bool) (random_get() % 2);
      assign_value(sat_vars, r, b);
      print("Decide x%=% @ level=%\n", r, b, level);
      array_add(assigns, create_log_var(r, level, -1));
      break;
    }
  }
}

Sat_Vars :: struct {
  tf_flags  : [..] u64;
  assigned: [..] u64;
  num_assigned: int;
  count: int;
}

unassign_value :: (sat_vars: *Sat_Vars, index: int) {
  arr_index := index / 64;
  bit_value := index % 64;
  sat_vars.assigned[arr_index] &= ~(cast(u64) 1 << bit_value);
  sat_vars.tf_flags[arr_index] &= ~(cast(u64) 1 << bit_value);
  sat_vars.num_assigned -= 1;
}

value_at :: (sat_vars: Sat_Vars, index: int)-> BoolAssign {
  arr_index := index / 64;
  bit_value := index % 64;

  assigned := sat_vars.assigned[arr_index] & (cast(u64) 1 << bit_value);
  if assigned == 0  // not assigned
    return BoolAssign.Unass;
  bool_val := sat_vars.tf_flags[arr_index] & (cast(u64) 1 << bit_value);
  if bool_val
    return BoolAssign.True;
  else
    return BoolAssign.False;
}

assign_value :: (sat_vars: *Sat_Vars, index: int, TF: bool) {
  arr_index := index / 64;
  bit_value := index % 64;

  sat_vars.assigned[arr_index] |= (cast(u64) 1 << bit_value);
  if TF {
    sat_vars.tf_flags[arr_index] |= (cast(u64) 1 << bit_value);
  } else {
    sat_vars.tf_flags[arr_index] &= ~(cast(u64) 1 << bit_value);
  }

  sat_vars.num_assigned += 1;
}

create_sat_vars :: inline (count: int)->Sat_Vars {
  sat_vars: Sat_Vars;
  sat_vars.count = count;
  sat_vars.num_assigned = 0;

  array_size := count / 64;
  if count % 64 > 0 
    array_size += 1;
  array_reserve(*sat_vars.tf_flags, array_size);
  array_reserve(*sat_vars.assigned, array_size);
  for i: 0..array_size-1 {
    array_add(*sat_vars.tf_flags, 0);
    array_add(*sat_vars.assigned, 0);
  }

  return sat_vars;
}

Clause   :: [..] Var;

Var :: enum_flags s32 {
  NOT       :: 0x8000_0000;
  SIGN_MASK :: 0x7fff_ffff;
  ONE :: 0x1;
}

BoolAssign :: enum s8 {
  True  :: 1;
  Flip  :: 1;
  False :: 0;
  Unass :: 0xFF;
}

get_var_num :: inline (v: Var) -> s64, BoolAssign {
  val := cast(s64) (Var.SIGN_MASK & v);
  not := cast(BoolAssign) (Var.NOT & v) <<< 1;    //(((Var.NOT & v) >> 31) & Var.ONE);
  //print("get_var_num: %\n", formatInt(cast(s8)not, base=16));
  return val, not;
}

for_expansion :: (self: *Sat_Vars, body: Code, f: For_Flags) #expand {
  for i: 0..self.count-1 {
    `it := value_at(<<self, i);
    `it_index := i;
    #insert body;
  }
}

print_clause :: (clause: Clause) {
  print("(");
  for var: clause {
    val, not := get_var_num(var);
    if not {
      print("-x% v", val);
    } else {
      print(" x% v", val);
    }
  }
  print(")\n");
}

boolean_constant_propagation :: (sat: *Sat_Vars, formula: [..]Clause, learnt_clauses: [..]Clause, assigns: *[..]LogVar, level: int)->Propagation_Status {
  TF := true;
  while TF {
    TF = false;
    for clause, clause_num: learnt_clauses {
      status, idx, val := unit_propagation(<<sat, clause);
      if status == {
      case Unit_Status.Nothing;
        // do nothing
      case Unit_Status.Conflict;
        // TODO: handle conflict!
        return Propagation_Status.Conflict;
      case Unit_Status.UnitPropagate;
        assign_value(sat, idx, val);
        array_add(assigns, create_log_var(idx, level, clause_num));
        print("assign x%=% @ level=%\n", idx, val, level);
        TF = true;
      case;
        assert(false);
      }
    }

    for clause, clause_num: formula {
      status, idx, val := unit_propagation(<<sat, clause);
      if status == {
      case Unit_Status.Nothing;
        // do nothing
      case Unit_Status.Conflict;
        // TODO: handle conflict!
        return Propagation_Status.Conflict;
      case Unit_Status.UnitPropagate;
        assign_value(sat, idx, val);
        array_add(assigns, create_log_var(idx, level, clause_num));
        print("assign x%=% @ level=%\n", idx, val, level);
        TF = true;
      case;
        assert(false);
      }
    }
  }
  return Propagation_Status.NoConflict;

  unit_propagation :: (sat: Sat_Vars, clause: Clause)->Unit_Status,int,bool {
    val_ret: s64 = ---;
    bool_ret: bool = ---;
    count := 0;

    for var : clause {
      val, not := get_var_num(var);
      assert(not == BoolAssign.True || not == BoolAssign.False, "not=%\n", not);
      bool_val := value_at(sat, val);
      if bool_val == BoolAssign.Unass {
        val_ret = val;
        bool_ret = cast(bool) (not ^ BoolAssign.Flip);
        count = count + 1;
        continue;
      } 
      bool_val ^= not;
      if bool_val == BoolAssign.True {
        return Unit_Status.Nothing, -1, false;
      }
    }
    if count > 1  // too many vars unassigned to use unit propagation
      return Unit_Status.Nothing, -1, false;

    if count == 0 // all vars unassigned, and there is a conflict.
      return Unit_Status.Conflict, -1, false;
    
    // unit propagate, there is one unassigned, and unit propagate it.
    return Unit_Status.UnitPropagate, val_ret, bool_ret;
  }

  Unit_Status :: enum u8 {
    UnitPropagate;
    Conflict;
    Nothing;
  }
}

Propagation_Status :: enum u8 {
  Conflict;
  NoConflict;
}

all_variables_assigned :: inline (using sat: Sat_Vars)->bool{
  return num_assigned >= count;
}

LogVar :: struct {
  var_num := -1;
  level := -1;
  clause_idx := -1;
}

create_log_var :: inline (var_num: int, level: int, clause_idx: int) -> LogVar {
  log: LogVar = ---;
  log.var_num = var_num;
  log.level = level;
  log.clause_idx = clause_idx;
  return log;
}

// get the last unique implication point
// TODO: we want to get the first unique implication point, not the last!!! But
// for now, use the last uip
analyze_conflict_last_uip :: (sat_vars: Sat_Vars, assigns: [..]LogVar, level: int)-> int, Clause {
  c: Clause;
  b := -1;
  for l: assigns {
    if l.clause_idx != -1 continue;
    print("LogVar: var_num=%, level=%, clause_idx=%\n", l.var_num, l.level, l.clause_idx);
    index := l.var_num; 
    val := value_at(sat_vars, index);
    if val == BoolAssign.True {
      array_add(*c, Var.NOT | cast(Var) index);
    } else if val == BoolAssign.False {
      array_add(*c, cast(Var) index);
    } else {
      assert(false, "Error. The value must either be True or False, NOT val %=%\n", index, val);
    }
    if l.level < level
      b = max(b, l.level);
  }

  return b, c;
}

/*analyze_conflict_first_uip :: (sat_vars: Sat_Vars, assigns: [..]LogVar, level: int)-> int, Clause {




}*/



init_priorities_vsids :: (num_vars: int, formula: [..]Clause)-> [..]float #must, [..]float #must {
  lit_priorities: [..]float;
  not_priorities: [..]float;
  array_reserve(*lit_priorities, num_vars);
  array_reserve(*not_priorities, num_vars);
  for i: 0..num_vars-1 {
    array_add(*lit_priorities, 0.0);
    array_add(*not_priorities, 0.0);
  }

  for clause: formula {
    for var : clause {
      val, not := get_var_num(var);
      if not {
        lit_priorities[val] += 1.0;
      } else {
        not_priorities[val] += 1.0;
      }
    }
  }
  return lit_priorities, not_priorities;
}

init_heap_vsids :: (num_vars: int, lit: [..]float, not: [..]float)->Heap {
  heap: Heap;
  array_reserve(*heap.arr, num_vars);
  for i: 0..num_vars-1 {
    enqueue(heap, i, lit, not);
  }
  return heap;
}

// max heap functions enqueue, dequeue
enqueue :: (using h: Heap, index: int, lit: [..]float, not: [..]float) {
  array_add(*arr, index);
  c := arr.count - 1;
  c_priority := max(lit[index], not[index]);
  while c > 0 {
    p := (c-1) / 2;
    val := arr[p];
    p_priority := max(lit[val], not[val]);
    if p < 0 || p_priority > c_priority
      break;
    swap(arr, p, c);
    c = p;
  }
}

dequeue :: (using h: Heap, lit: [..]float, not: [..]float)-> int, float {
  ret := arr[0];
  ret_p := max(lit[ret], not[ret]);
  i := arr.count - 1;
  arr[0] = arr[i];

  p := 0;
  p_priority := max(lit[arr[p]], not[arr[p]]);
  while p < i {
    l := 2*p + 1;
    r := 2*p + 2;
    c := -1;
    if l > i 
      break;
    c = l;
    c_priority: float = ---;
    if r < i { 
      r_priority := max(lit[arr[r]], not[arr[r]]);
      l_priority := max(lit[arr[l]], not[arr[l]]);
      if r_priority > l_priority {
        c = r;
        c_priority = r_priority;
      } else {
        c_priority = l_priority;
      }
    }
    if p_priority > c_priority
      break;
    swap(arr, p, c);
    p = c;
  }

  pop(*arr);
  return ret, ret_p;
}

count :: inline (using h: Heap)-> int {
  return arr.count;
}

swap :: inline (arr: []int, p: int, c: int) #expand {
  t := arr[p];
  arr[p] = arr[c];
  arr[c] = t;
}

Heap :: struct {
  arr: [..] int;
}
