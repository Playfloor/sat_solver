#import "Basic";
#import "File";
#import "String";

SAT :: enum s8 { UNASSIGNED :: TRUE|FALSE; FALSE :: 1; TRUE :: 2; CONFLICT :: 4; OKAY :: 0; }


Clause :: [..] int;

parse_sat_file :: (file_name: string)-> int, [..]Clause {
  text := read_entire_file(file_name);
  lines := split(text, "\n");
  clauses : [..]Clause;
  num_variables := -1;

  for line : lines {
    tokens := split(line, " ");
    if tokens.count == 0 {
      continue;
    }
    if equal(tokens[0], "c") {
      continue;
    }

    else if equal(tokens[0], "p") {
      num_variables = string_to_int(tokens[2]);
      num_clauses   := string_to_int(tokens[3]);
      array_reserve(*clauses, num_clauses);
    } else {
      clause : Clause;
      for token : tokens {
        val := string_to_int(token);
        if val == 0
          break;
        array_add(*clause, val);
      }
      array_add(*clauses, clause);
    }
  }
  return num_variables, clauses;
}

naive_sat_solver :: (vars: [..]SAT, clauses: [..]Clause, level:=0)->bool {

  is_satisfiable :: (vars: [..]SAT, clauses: [..]Clause)->bool {
    for clause : clauses {
      cl := SAT.FALSE;
      for var : clause{
        bool_value : SAT = ---;
        if var < 0 {
          var = -var;
          bool_value = vars[var-1] ^ SAT.TRUE;
        } else {
          bool_value = vars[var-1];
        }

        cl = cl | bool_value;
      }
      if cl == SAT.FALSE {
        return false;
      }
    }
    return true;
  }


  if level >= vars.count then {
    return is_satisfiable(vars, clauses);
  }
  
  vars[level] = SAT.TRUE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT.FALSE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT.UNASSIGNED;
  return false;
}

GraphNode :: struct {
  clause := -1;
  level  := -1;
  edges  : [..] int;
}

ImplicationGraph :: [..] GraphNode;

boolean_constant_propagation :: (f: [..]Clause, a: [..]SAT, graph: ImplicationGraph, level := 0)-> SAT {
  while true {
    cont := false;
    for clause : f {
      index, val := unit_propagation(a, clause);
      if val == SAT.CONFLICT {
        return SAT.CONFLICT;
      }
      if index != -1 {
        a[index] = val;
        cont = true;
      }
    }

    if cont == false then break;
  }

  return SAT.OKAY;

  unit_propagation :: (a: [..]SAT, clause : Clause)->int, SAT {
    count := 0;
    index := -1;
    value := SAT.UNASSIGNED;
    for var : clause {
      if var < 0 {
        var = -var - 1;
        if a[var] == SAT.FALSE then return -1, SAT.UNASSIGNED;
        if a[var] == SAT.UNASSIGNED {
          count = count + 1;
          index = var;
          value = SAT.FALSE;
        }
      } else {
        var = var - 1;
        if a[var] == SAT.TRUE then return -1, SAT.UNASSIGNED;
        if a[var] == SAT.UNASSIGNED {
          count = count + 1;
          index = var;
          value = SAT.TRUE;
        }
      }
      if count > 1 then return -1, SAT.UNASSIGNED;
    }
    if count == 1 {
      return index, value;
    } else {
      assert(count == 0);
      return -1, SAT.CONFLICT;
    }
  }

  create_node :: (graph : ImplicationGraph, level: int, clause_num: int) {

  }

}

conflict_drive_clause_learning :: (num_vars: int, f: [..]Clause)->bool, [..]SAT {
  a : [..] SAT;
  graph : ImplicationGraph;
  init_vars(*a, *graph, num_vars);
  if boolean_constant_propagation(f, a, graph) {
    return false, a;
  }

  level := 0;
  while has_unassigned_variables(a) {
    level = level + 1;
    decide(f, a);    
    while boolean_constant_propagation(f, a, graph, level) {
      b, c := analyze_conflict();
      array_add(*f, c);
      if b < 0 {
        return false, a;
      } else {
        backtrack(f, a, b);
        level = b;
      }
    }
  }

  return true, a;

  // helper functions.
  init_vars :: (a: *[..]SAT, G: *ImplicationGraph, num_vars: int) {
    array_reserve(a, num_vars);
    array_reserve(G, num_vars+1);
    for i: 0..num_vars-1 {
      node: GraphNode;
      node.clause=-1;
      node.level=-1;
      array_add(a, SAT.UNASSIGNED);
      array_add(G, node);
    }
    node: GraphNode;
    node.clause=-1;
    node.level=-1;
    array_add(G, node);
  }

  backtrack :: (f: [..]Clause, a: [..]SAT, b: int) {

  }

  analyze_conflict :: ()->(int, Clause) {
    c : Clause;
    return -1, c;
  }

  decide :: (f: [..]Clause, a: [..]SAT) {

  }

  has_unassigned_variables :: (a: [..]SAT)->bool #expand {
    for var : a
      if var == SAT.UNASSIGNED return true;
    return false;
  }


  // TODO: just temporary. this is just useless
  is_satisfiable :: (vars: [..]SAT, clauses: [..]Clause)->bool {
    for clause : clauses {
      cl := SAT.FALSE;
      for var : clause{
        is_not := var < 0;
        if is_not {
          var = -var - 1;
        } else {
          var = var - 1;
        }

        bool_value : SAT = SAT.FALSE;
        if is_not && vars[var]==SAT.FALSE {
          bool_value = SAT.TRUE;
        } else if !is_not && vars[var]==SAT.TRUE {
          bool_value = SAT.TRUE;
        }
 
        if bool_value == SAT.TRUE {
          cl = SAT.TRUE;
          break;
        }
      }
      if cl == SAT.FALSE {
        return false;
      }
    }
    return true;
  }

}

main :: () {
  args := get_command_line_arguments();
  if args.count == 1 {
    print("Please supply a *.cnf sat file to the program.\n");
    return;
  }

  // parse the sat file
  for i: 1..args.count - 1 {
    file_name := args[i];
    print("-----------------------\n");
    print("%\n", file_name);

    num_vars, clauses := parse_sat_file(file_name);
    // sat solver
    sat, vars := conflict_drive_clause_learning(num_vars, clauses);
 
    if sat {
      print("sat\n");
    } else {
      for var : vars {
        print("x%=%,  ", it_index, var);
      }
      print("unsat\n");
    }
  }
}


