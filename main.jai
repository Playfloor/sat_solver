#import "Basic";
#import "File";
#import "String";

main :: () {
  args := get_command_line_arguments();
  if args.count == 1 {
    print("Please supply a *.cnf sat file to the program.\n");
    return;
  }

  file_name := args[1];
  num_vars, clauses := parse_sat_file(file_name);
  sat, sat_vars := search(num_vars, clauses);

  if sat {
    for clause: clauses {
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
  stack: [..]Var;

  while true {
    status := boolean_constant_propagation(*sat_vars, formula);
    if status == Propagation_Status.Conflict {
      return false, sat_vars; // TODO
    }

    if all_variables_assigned(sat_vars) then
      break;
    decide(*sat_vars, *stack);
  }

  return true, sat_vars;
}

init_decide := true; // TODO: temporary global

decide :: (sat_vars: *Sat_Vars, stack: *[..]Var) #expand {
  if init_decide {
    for val, idx: sat_vars {
      if val == BoolAssign.Unass {
        array_add(stack, Var.NOT | cast(Var) idx);
        array_add(stack, cast(Var) idx);
        break;
      }
    }
    init_decide = false;
  }
  
  top := pop(stack);
  val, not := get_var_num(top);
  if not {
    assign_value(sat_vars, val, false);
    print("Decide x%=false\n", val);
  } else {
    assign_value(sat_vars, val, true);
    print("Decide x%=true\n", val);
  }

  for val, idx: sat_vars {
    if val == BoolAssign.Unass {
      array_add(stack, Var.NOT | cast(Var) idx);
      array_add(stack, cast(Var) idx);
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
  not := cast(BoolAssign) (((Var.NOT & v) >> 31) & Var.ONE);
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

boolean_constant_propagation :: (sat: *Sat_Vars, formula: [..]Clause)->Propagation_Status {
  TF := true;
  while TF {
    TF = false;
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
        print("assign x%=%\n", idx, val);
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



