open SVMAST

module State = 

    let add_value_to_register (registers :  Map<Register, Literal>) (target : Register) (value : Literal) : Map<Register, Literal> =
        match registers.TryFind(target) with
        | None -> failwith ("Register not found exception (does the register exist?): " + string target)
        | _ -> registers.Add(target, value)

    let add_value_to_address (memory : Map<int, Literal>) (target : int) (value : Literal) : Map<int, Literal> =
        match memory.TryFind(target) with
        | None -> failwith ("Memory location not found exception (is there enough memory available?): " + string target)
        | _ -> memory.Add(target, value)

    type State =
        {
            PC : int
            ProgramArea : Program
            Memory : Map<int, Literal>
            Registers : Map<Register, Literal>
            Labels : Map<string, int>
        }

        static member Empty(program : Program, memSize : int) =
            let rec get_labels length (program: Program) =
                match program with
                | [] -> []
                | Label (id, position) :: xs -> (id, length - xs.Length) :: get_labels length xs
                | _::xs -> get_labels length xs
            {
                PC = 0
                ProgramArea = program
                Memory = [for i in [0..memSize] do yield (i, Integer(0, (0, 0)))] |> Map.ofSeq 
                Registers = [(Reg1, Integer (0, (0,0)))
                             (Reg2, Integer (0, (0,0)))
                             (Reg3, Integer (0, (0,0)))
                             (Reg4, Integer (0, (0,0)))] |> Map.ofSeq
                Labels = program |> get_labels program.Length |> Map.ofSeq
            }

            member this.IsEOF() = 
                this.PC >= this.ProgramArea.Length
            member this.Step() : State =
                let get_value_of_literal (literal : Literal) (position : Position)=
                    match literal with
                    | Address(addr) ->
                        match addr with
                        | Integer(memoryAddress, _) -> this.Memory.[memoryAddress]
                        | Register(register, position) ->
                            match this.Registers.[register] with
                            |Integer(value, pos) -> this.Memory.[value]
                            |_ -> failwith ("Wrong argument Exception, expected Integer at: " + string position) 
                        | _ -> failwith ("Wrong argument Exception, expected Integer at: " + string position)
                    | Register(register, position) -> this.Registers.[register]
                    | _ ->  literal

                let current_instruction = this.ProgramArea.[this.PC]
                match current_instruction with
                | Nop (position) ->
                    { this with PC = this.PC + 1 }

                | Mov (literalSource, literalTarget, position) ->
                    match literalSource with
                    | Address(addr) ->
                        match addr with
                        | Integer(memoryAddress, position) ->
                            { this with Memory = add_value_to_address this.Memory memoryAddress (get_value_of_literal literalTarget position); PC = this.PC + 1 }
                        | Register(register, position) ->
                            match this.Registers.[register] with
                            | Integer(registerValue, _) ->
                                { this with Memory = add_value_to_address this.Memory registerValue (get_value_of_literal literalTarget position); PC = this.PC + 1 }
                            | _ -> failwith ("Wrong argument Exception, expected Integer at: " + string position)
                        | _ -> failwith ("Wrong argument Exception, expected Integer or Register at: " + string position)
                    | Register(register, position) -> 
                            { this with Registers = add_value_to_register this.Registers register (get_value_of_literal literalTarget position); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for MOV at: " + string position)

                | And (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        match (registerValue, literalValue) with
                        | x, y when x >= 0 && y >= 0 ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(1, (0, 0))); PC = this.PC + 1 }
                        | _ ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(0, (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for AND at: " + string position)

                | Or (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        match (registerValue, literalValue) with
                        | x, y when x < 0 && y < 0 ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(0, (0, 0))); PC = this.PC + 1 }
                        | _ ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(1, (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for OR at: " + string position)

                | Not (register, position) ->
                    match (this.Registers.[register]) with
                    | Integer(registerValue, _) ->
                        match registerValue with
                        | x when x > 0 ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(-1, (0, 0))); PC = this.PC + 1 }
                        | _ ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(0, (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for NOT at: " + string position)

                | Mod (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Integer((registerValue % literalValue), (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Float((registerValue % literalValue), (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for MOD at: " + string position)

                | Add (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Integer((registerValue + literalValue), (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Float((registerValue + literalValue), (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for Add at: " + string position)

                | Sub (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Integer((registerValue - literalValue), (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Float((registerValue - literalValue), (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for Sub at: " + string position)

                | Mul (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Integer((registerValue * literalValue), (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Float((registerValue * literalValue), (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for Mul at: " + string position)

                | Div (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Integer((registerValue / literalValue), (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        { this with Registers = add_value_to_register this.Registers register (Float((registerValue / literalValue), (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for Div at: " + string position)

                | Cmp (register, literal, position) ->
                    match (this.Registers.[register], get_value_of_literal literal position) with
                    | Integer(registerValue, _), Integer(literalValue, _) ->
                        match (registerValue, literalValue) with
                        | x, y when x < y ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(-1, (0, 0))); PC = this.PC + 1 }
                        | x, y when x = y ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(0, (0, 0))); PC = this.PC + 1 }
                        | _ ->
                            { this with Registers = add_value_to_register this.Registers register (Integer(1, (0, 0))); PC = this.PC + 1 }
                    | Float(registerValue, _), Float(literalValue, _) ->
                        match (registerValue, literalValue) with
                        | x, y when x < y ->
                            { this with Registers = add_value_to_register this.Registers register (Float(-1.0, (0, 0))); PC = this.PC + 1 }
                        | x, y when x = y ->
                            { this with Registers = add_value_to_register this.Registers register (Float(0.0, (0, 0))); PC = this.PC + 1 }
                        | _ ->
                            { this with Registers = add_value_to_register this.Registers register (Float(1.0, (0, 0))); PC = this.PC + 1 }
                    | _ -> failwith ("Wrong argument Exception for Cmp at: " + string position)

                | Label (id, position) ->
                    { this with PC = this.PC + 1}

                | Jmp (id, position) ->
                    match this.Labels.TryFind(id) with
                    | None -> failwith ("Label not found Exception at: ")
                    | Some(pcLine) -> {this with PC = pcLine}

                | Jc(id, register, position) ->
                  match this.Registers.[register] with
                  |Integer(registerValue, _) when registerValue > 0 ->  
                    match this.Labels.TryFind(id) with
                    | None -> failwith ("Label not found Exception at: " + string position)
                    | Some(pcLine) ->
                      {this with PC = pcLine} 
                  |Float(registerValue, position) when registerValue >= 0.0 ->  
                    match this.Labels.TryFind(id) with
                    | None -> failwith ("Label not found Exception at: " + string position)
                    | Some(pcLine) ->
                      {this with PC = pcLine} 
                  |_ -> {this with PC = this.PC + 1}   
        

                | Jeq(id, register, position) ->
                  match this.Registers.[register] with
                  |Integer(registerValue, position) when registerValue = 0 ->  
                    match this.Labels.TryFind(id) with
                    | None -> failwith ("Label not found Exception at: " + string position)
                    | Some(pcLine) ->
                      {this with PC = pcLine} 
                  |Float(value, position) when value = 0.0 ->  
                    match this.Labels.TryFind(id) with
                    | None -> failwith ("Label not found Exception at: " + string position)
                    | Some(pcLine) ->
                      {this with PC = pcLine} 
                  |_ -> {this with PC = this.PC + 1}

                | _ -> failwith ("Not supported expression: " + string current_instruction)

            override m.ToString() = 
                "{\n" +
                "\tPC : " + (if m.IsEOF() then "EOF" else string m.PC) + "\n" +
                "\tCurrentInstruction: " + (if m.IsEOF() then "null" else sprintf "%A" m.ProgramArea.[m.PC]) + "\n" +
                "\tMemory: \n" + (m.Memory |>
                                    Map.toSeq |>
                                    Seq.fold(fun s (k:int, v:Literal) ->
                                        s + "\t[" + string k + "] -> " + string v + if ((k+1) % 5 = 0 && k <> 1) then "\n" else null) "") +
                "\n\tRegisters: \n" + (m.Registers |>
                                        Map.toSeq |>
                                        Seq.fold(fun s (id:Register, v:Literal) -> 
                                            s + "\t" + string id + "-> " + string v) "")  +
                "\n}"

open System
open System.IO
open ParserUtils
open SVM
open Microsoft.FSharp.Text.Lexing
open State

let parseFile (fileName : string) =
  let inputChannel = new StreamReader(fileName)
  let lexbuf = LexBuffer<char>.FromTextReader inputChannel
  let parsedAST = Parser.start Lexer.tokenstream lexbuf
  parsedAST

let rec eval (state : State) =
    if state.IsEOF() then printfn "The program is over..."
    else
        let memory' = state.Step()
        printfn "%A" (string memory')
        System.Console.ReadLine() |> ignore
        eval memory'

[<EntryPoint>]
let main argv =
  try
    if argv.Length = 2 then
      let ast = parseFile argv.[0]
      let memSize = argv.[1] |> int
      do printfn "%A" ast
      let memory = State.Empty(ast, memSize)
      eval memory
      0
    else
      do printfn "You must specify a command line argument containing the path to the program source file and the size of the memory"
      1
  with
  | ParseError(msg,row,col) ->
      do printfn "Parse Error: %s at line %d column %d" msg row col
      1
  | :? Exception as e ->
      do printfn "%s" e.Message
      1
