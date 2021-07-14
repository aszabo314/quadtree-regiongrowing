open System
open Aardvark.Base
open Aardvark.Rendering
open Aardvark.Rendering.Text
open Aardvark.SceneGraph
open Aardvark.Application
open Aardvark.Application.Slim
open FSharp.Data.Adaptive
open System.Collections.Generic
open System.Threading
open FSharp.Data.Adaptive
let mutable maxLvl = -1
let mutable ct = 0
let idx() = 
    let res = ct
    ct <- ct+1
    res

type Dir = Left | Up | Right | Down

[<AutoOpen>]
module rec Stuff =
    type NodeData =
        {
            idx : int
            density : float
            centroid : V2d
            mutable parent : Option<QuadTree>
            location : list<int>
            level : int
        }

    [<CustomEquality; NoComparison>]
    type QuadTree =
    | Node of NodeData*bl:QuadTree*tl:QuadTree*tr:QuadTree*br:QuadTree
    | Leaf of NodeData
        with 
            member x.Centroid = 
                match x with
                | Leaf d -> d.centroid
                | Node (d,_,_,_,_) -> d.centroid
                
            member x.Id = 
                match x with
                | Leaf d -> d.idx
                | Node (d,_,_,_,_) -> d.idx
                
            member x.Level = 
                match x with
                | Leaf d -> d.level
                | Node (d,_,_,_,_) -> d.level

            override x.GetHashCode() = x.Id
            override x.Equals(o) =
                match o with 
                | :? QuadTree as oq -> 
                    x.Id = oq.Id
                | _ -> false

[<ReferenceEquality>]
type Traversed =
    {
        startIdx : int
        visited : MapExt<int,QuadTree>
        pending : HashSet<QuadTree>
    }

module Traversed =
    let Empty = 
        {
            startIdx = -1
            visited = MapExt.empty
            pending = HashSet.Empty
        }

module QuadTree =
    let getData (q : QuadTree) =
        match q with 
        | Leaf d -> d
        | Node(d,_,_,_,_) -> d

    let path (q : QuadTree) =
        (getData q).location

    let generate leafThreshold =
        maxLvl <- 0
        ct <- 0
        let rand = RandomSystem()
        let randBetween mi ma = rand.UniformDouble() * (ma-mi) + mi
        let lvl0Density = 1.0
        let rec build (mi : V2d) (ma : V2d) (locationCode : list<int>) (density : float) (level : int) =
            if level > maxLvl then maxLvl <- level
            if density <= leafThreshold then Leaf {centroid = (mi+ma)/2.0; idx = idx(); density = density; parent = None; location = locationCode; level = level}
            else
                let r = ma-mi
                let p00 = mi
                let p10 = V2d(mi.X + r.X/2.0, mi.Y)
                let p20 = V2d(ma.X,           mi.Y)
                let p01 = V2d(mi.X,           mi.Y + r.Y/2.0)
                let p11 = V2d(mi.X + r.X/2.0, mi.Y + r.Y/2.0)
                let p21 = V2d(ma.X,           mi.Y + r.Y/2.0)
                let p02 = V2d(mi.X,           ma.Y)
                let p12 = V2d(mi.X + r.X/2.0, ma.Y)
                let p22 = ma

                let parts = Array.init 4 (fun _ -> randBetween 0.0 density) |> Array.sort
                //let parts = [|0.25; 0.5; 0.75; 1.0|] |> Array.map (fun t -> t*density)
                let bl = build p01 p12 (locationCode@[2]) parts.[0] (level+1)
                let tl = build p00 p11 (locationCode@[0]) (parts.[1]-parts.[0]) (level+1)
                let tr = build p10 p21 (locationCode@[1]) (parts.[2]-parts.[1]) (level+1)
                let br = build p11 p22 (locationCode@[3]) (parts.[3]-parts.[2]) (level+1)
                Node({centroid = (mi+ma)/2.0; idx = idx(); density = density; parent = None; location = locationCode; level = level}, bl, tl, tr, br)
        let rec fixParents (p : Option<QuadTree>) (q : QuadTree) =
            match q with 
            | Leaf d -> d.parent <- p
            | Node(d, bl, tl, tr, br) -> 
                d.parent <- p
                fixParents (Some q) bl
                fixParents (Some q) tl
                fixParents (Some q) tr
                fixParents (Some q) br

        let res = build V2d.NN V2d.II [] lvl0Density 0
        fixParents None res
        res

    let toSg (quad : aval<QuadTree>) (traversal : aval<Traversed>) =
        let rec traverse (mi : V2d) (ma : V2d) (q : QuadTree) (t : Traversed) =
            let posred d =
                if t.visited |> MapExt.containsKey d.idx then 
                    [|
                        V2d(mi.X,mi.Y);V2d(mi.X,ma.Y);V2d(ma.X,ma.Y);
                        V2d(mi.X,mi.Y);V2d(ma.X,mi.Y);V2d(ma.X,ma.Y);
                    |]
                else [||]
            let posgrn d =
                if t.pending |> HashSet.contains d then 
                    [|V2d(mi.X,mi.Y);V2d(mi.X,ma.Y);
                      V2d(mi.X,ma.Y);V2d(ma.X,ma.Y);
                      V2d(ma.X,ma.Y);V2d(ma.X,mi.Y);
                      V2d(ma.X,mi.Y);V2d(mi.X,mi.Y);
                    |]
                else [||]
            let posylo d =
                if t.startIdx = d.idx then 
                    [|
                        V2d(mi.X,mi.Y);V2d(mi.X,ma.Y);V2d(ma.X,ma.Y);
                        V2d(mi.X,mi.Y);V2d(ma.X,mi.Y);V2d(ma.X,ma.Y);
                    |]
                else [||]
            match q with 
            | Leaf d -> 
                let pos = [|V2d(mi.X,mi.Y);V2d(mi.X,ma.Y);
                  V2d(mi.X,ma.Y);V2d(ma.X,ma.Y);
                  V2d(ma.X,ma.Y);V2d(ma.X,mi.Y);
                  V2d(ma.X,mi.Y);V2d(mi.X,mi.Y);
                |]
                pos, posred d, posylo d, posgrn q
            | Node(d, bl, tl, tr, br) -> 
                let r = ma-mi
                let p00 = mi
                let p10 = V2d(mi.X + r.X/2.0, mi.Y)
                let p20 = V2d(ma.X,           mi.Y)
                let p01 = V2d(mi.X,           mi.Y + r.Y/2.0)
                let p11 = V2d(mi.X + r.X/2.0, mi.Y + r.Y/2.0)
                let p21 = V2d(ma.X,           mi.Y + r.Y/2.0)
                let p02 = V2d(mi.X,           ma.Y)
                let p12 = V2d(mi.X + r.X/2.0, ma.Y)
                let p22 = ma
                let (pa0,pr0,py0,pg0) = traverse p00 p11 tl t
                let (pa1,pr1,py1,pg1) = traverse p10 p21 tr t
                let (pa2,pr2,py2,pg2) = traverse p01 p12 bl t
                let (pa3,pr3,py3,pg3) = traverse p11 p22 br t

                Array.concat [pa0;pa1;pa2;pa3], 
                Array.concat [pr0;pr1;pr2;pr3;posred d],
                Array.concat [py0;py1;py2;py3;posylo d],
                Array.concat [pg0;pg1;pg2;pg3;posgrn q]
        let positions mi ma q t =
            let res = traverse mi ma q t
            res

        let ps = AVal.map2 (fun q t -> positions (V2d(-1.0,1.0)) (V2d(1.0,-1.0)) q t) quad traversal

        let whiteBoxes = ps |> AVal.map (fun (d,_,_,_) -> d)
        let redTris =    ps |> AVal.map (fun (_,d,_,_) -> d)
        let yloTris =    ps |> AVal.map (fun (_,_,d,_) -> d)
        let grnLines =   ps |> AVal.map (fun (_,_,_,d) -> d)

        let pass0 = RenderPass.main
        let pass1 = RenderPass.after "asdasd" RenderPassOrder.Arbitrary RenderPass.main
        let pass2 = RenderPass.after "asdasd21354235" RenderPassOrder.Arbitrary pass1
        let pass3 = RenderPass.after "43673457reth345z" RenderPassOrder.Arbitrary pass2

        let whiteSg =
            Sg.draw IndexedGeometryMode.LineList
            |> Sg.vertexAttribute DefaultSemantic.Positions whiteBoxes
            |> Sg.shader {
                do! DefaultSurfaces.constantColor C4f.White
                do! DefaultSurfaces.thickLine
            }
            |> Sg.uniform "LineWidth" (AVal.constant 0.5)
            |> Sg.pass pass0
        let redSg =
            Sg.draw IndexedGeometryMode.TriangleList
            |> Sg.vertexAttribute DefaultSemantic.Positions redTris
            |> Sg.shader {
                do! DefaultSurfaces.constantColor (C4f(1.0f,0.0f,0.0f,0.25f))
            }
            |> Sg.blendMode (AVal.constant BlendMode.Blend)
            |> Sg.pass pass1
        let yloSg =
            Sg.draw IndexedGeometryMode.TriangleList
            |> Sg.vertexAttribute DefaultSemantic.Positions yloTris
            |> Sg.shader {
                do! DefaultSurfaces.constantColor (C4f(0.0f,1.0f,0.0f,0.25f))
            }
            |> Sg.blendMode (AVal.constant BlendMode.Blend)
            |> Sg.pass pass2
        let grnSg =
            Sg.draw IndexedGeometryMode.LineList
            |> Sg.vertexAttribute DefaultSemantic.Positions grnLines
            |> Sg.shader {
                do! DefaultSurfaces.constantColor C4f.Blue
                do! DefaultSurfaces.thickLine
            }
            |> Sg.uniform "LineWidth" (AVal.constant 1.25)
            |> Sg.depthTest (AVal.constant DepthTest.None)
            |> Sg.pass pass3
            
        Sg.ofList [whiteSg;redSg;yloSg;grnSg]

    let rec findIdx (i : int) (q : QuadTree) =
        match q with 
        | Leaf(d) -> if d.idx = i then Some q else None
        | Node(d,bl,tl,tr,br) -> 
            if d.idx = i then Some q 
            else 
                [
                    findIdx i bl
                    findIdx i tl
                    findIdx i tr
                    findIdx i br
                ] |> List.choose id |> List.tryHead
    let rec findPath (p : list<int>) (q : QuadTree) =
        match q with 
        | Leaf _ -> 
            match p with 
            | [] -> Some q
            | _ -> None
        | Node(_,bl,tl,tr,br) -> 
            match p with 
            | [] -> Some q
            | l::remaining -> 
                match l with 
                | 0 -> findPath remaining tl
                | 1 -> findPath remaining tr
                | 2 -> findPath remaining bl
                | 3 -> findPath remaining br
                | _ -> failwith ""

    let nodesOfLevel (l : int) (q : QuadTree) =
        let l = clamp 0 maxLvl l
        let rec traverse (i : int) (q : QuadTree) =
            match q with 
            | Leaf _ -> 
                if i = 0 then [q] else []
            | Node(_,bl,tl,tr,br) -> 
                if i = 0 then [q] else
                    List.concat [
                        traverse (i-1) bl
                        traverse (i-1) tl
                        traverse (i-1) tr
                        traverse (i-1) br
                    ]
        traverse l q

    let rec strictlyContainsPath (outer : list<int>) (inner : list<int>) = 
        match outer,inner with 
        | [], [] -> true
        | [], _ -> true
        | _, [] -> false
        | o::router, i::rinner -> 
            (o=i)&&(strictlyContainsPath router rinner)

    let strictlyContains (outer : QuadTree) (inner : QuadTree) =
        strictlyContainsPath (getData outer).location (getData inner).location 

    let rec containsOrEqualPath (outer : list<int>) (inner : list<int>) = 
        match outer,inner with 
        | [], [] -> true
        | [], _ -> true
        | _, [] -> false
        | o::router, i::rinner -> 
            (o=i)&&(containsOrEqualPath router rinner)

    let containsOrEqual (outer : QuadTree) (inner : QuadTree) =
        containsOrEqualPath (getData outer).location (getData inner).location 

module Traversal =
    // http://web.archive.org/web/20120907211934/http://ww1.ucmss.com/books/LFS/CSREA2006/MSV4517.pdf
    let getNeighbor (d : Dir) (q : QuadTree) (root : QuadTree) =
        match (QuadTree.getData q).location with 
        | [] -> None
        | l -> 
            let rec constructPath (currentDir : Option<Dir>) (currentPath : list<int>) =
                match currentDir with 
                | None -> Some currentPath
                | Some dir -> 
                    match currentPath with 
                    | loc::remaining -> 
                        let (newLoc, newDir) =
                            match loc with 
                            | 0 -> 
                                match dir with 
                                | Right -> 1,None
                                | Left  -> 1,Some Left
                                | Down  -> 2,None
                                | Up    -> 2,Some Up
                            | 1 -> 
                                match dir with 
                                | Right -> 0,Some Right
                                | Left  -> 0,None
                                | Down  -> 3,None
                                | Up    -> 3,Some Up
                            | 2 -> 
                                match dir with 
                                | Right -> 3,None
                                | Left  -> 3,Some Left
                                | Down  -> 0,Some Down
                                | Up    -> 0,None
                            | 3 -> 
                                match dir with 
                                | Right -> 2,Some Right
                                | Left  -> 2,None
                                | Down  -> 1,Some Down
                                | Up    -> 1,None
                            | _ -> failwith ""
                        constructPath newDir remaining 
                        |> Option.map (fun res -> newLoc::res)
                    | [] -> None
            constructPath (Some d) (List.rev l)
            |> Option.bind (fun path ->
                QuadTree.findPath (List.rev path) root
            )

    let regionGrowFromRandomStart (startLevel : int) (desiredLevel : unit -> int) (root : QuadTree) (resCb : Traversed -> unit) =
        let rand = RandomSystem()
        let startNode =
            let nodes = QuadTree.nodesOfLevel startLevel root |> List.toArray
            nodes.[rand.UniformInt(nodes.Length)]
        let startPoint = startNode.Centroid
        let mutable finished = MapExt.empty
        let mutable visited = HashSet.empty
        let mutable queue = HashSet.empty
        let mutable currentLevel = startLevel

        let enqueue (q : QuadTree) =
            if not (visited |> HashSet.contains q) then 
                queue <- queue |> HashSet.add q
                
        let tryDequeue() =
            let closest = queue |> HashSet.fold (fun mi c -> match mi with None -> Some c | Some m -> if Vec.distance c.Centroid startPoint < Vec.distance m.Centroid startPoint then Some c else Some m) None
            match closest with 
            | None -> None 
            | Some c -> 
                queue <- queue |> HashSet.remove c
                Some c

        let rec enqueueNeighbor (d : Dir) (q : QuadTree) =
            match getNeighbor d q root with 
            | Some n -> enqueue n
            | None -> 
                match (QuadTree.getData q).parent with 
                | Some p -> 
                    enqueueNeighbor d p
                | None -> ()

        enqueue startNode
        let mutable running = true
        while running do
            //let q = dequeue()
            //finished <- finished |> MapExt.add (QuadTree.getData q).idx true
            //match getNeighbor Left q root with 
            //| None -> ()
            //| Some n -> 
            //    queue.Add(n)
            //Thread.Sleep 15
            //resCb {startIdx = (QuadTree.getData startNode).idx; visited = finished; pending = queue |> CSharpList.toArray |> HashSet.ofArray}

            currentLevel <- desiredLevel()
            match tryDequeue() with 
            | None -> running <- false
            | Some q ->
                visited <- visited |> HashSet.add q
                let mutable skip = false
                if q.Level < currentLevel then 
                    match q with 
                    | Leaf _ -> ()
                    | Node(_,bl,tl,tr,br) -> 
                        enqueue bl
                        enqueue tl
                        enqueue tr
                        enqueue br
                        skip <- true
                if not skip then 
                    let mutable skipCurrent = false
                    if q.Level > currentLevel then 
                        match (QuadTree.getData q).parent with
                        | None -> failwith "cant collapse root"
                        | Some parent -> 
                            let evil = finished |> MapExt.values |> Seq.exists(fun f -> QuadTree.containsOrEqual parent f)
                            if evil then 
                                ()
                            else 
                                enqueue parent
                                skipCurrent <- true
                    if not skipCurrent then 
                        if not (finished |> MapExt.values |> Seq.exists(fun f -> QuadTree.containsOrEqual q f)) && 
                           not (finished |> MapExt.values |> Seq.exists(fun f -> QuadTree.containsOrEqual f q)) then
                            finished <- finished |> MapExt.add q.Id q
                        enqueueNeighbor Left q
                        enqueueNeighbor Up q
                        enqueueNeighbor Right q
                        enqueueNeighbor Down q

                resCb {startIdx = startNode.Id; visited = finished; pending = queue}
                Thread.Sleep 100
                
        Log.line "done"
        resCb {startIdx = startNode.Id; visited = finished; pending = queue}

[<EntryPoint;STAThread>]
let main argv = 
    let mutable ver = 0
    let create() =
        Log.startTimed "generate ..."    
        let res = QuadTree.generate 0.00005
        ver <- ver+1
        Log.stop()
        res
    let q = AVal.init (create())

    Aardvark.Init()

    let traversed = cval Traversed.Empty
    let startLevel = cval 6
    let numberInput = cval [startLevel.Value]
    let numberInputDisplay = numberInput |> AVal.map ((List.fold (fun (e,s) d -> (e+1),(s+d*Fun.Pown(10,e))) (0,0))>>snd)
    let desiredLevel = cval startLevel.Value

    let doIt = 
        async {
            do! Async.SwitchToNewThread()
            let mutable lastVer = ver
            while true do 
                do! Async.Sleep 5
                if lastVer <> ver then 
                    lastVer <- ver 
                    Traversal.regionGrowFromRandomStart (startLevel |> AVal.force) (fun _ -> desiredLevel |> AVal.force) (q |> AVal.force) (fun t -> transact (fun _ -> traversed.Value <- t))
        } |> Async.Start

    let sg = QuadTree.toSg q traversed

    use app = new OpenGlApplication()
    use win = app.CreateGameWindow(4)
    
    win.Keyboard.DownWithRepeats.Values.Add (fun k -> 
        match k with 
        | Keys.Space -> transact (fun _ -> q.Value <- create())
        | Keys.O -> transact (fun _ -> startLevel.Value <- max (startLevel.Value-1) 0)
        | Keys.P -> transact (fun _ -> startLevel.Value <- min (startLevel.Value+1) maxLvl)
        | Keys.D0 -> transact (fun _ -> numberInput.Value <- 0::numberInput.Value)
        | Keys.D1 -> transact (fun _ -> numberInput.Value <- 1::numberInput.Value)
        | Keys.D2 -> transact (fun _ -> numberInput.Value <- 2::numberInput.Value)
        | Keys.D3 -> transact (fun _ -> numberInput.Value <- 3::numberInput.Value)
        | Keys.D4 -> transact (fun _ -> numberInput.Value <- 4::numberInput.Value)
        | Keys.D5 -> transact (fun _ -> numberInput.Value <- 5::numberInput.Value)
        | Keys.D6 -> transact (fun _ -> numberInput.Value <- 6::numberInput.Value)
        | Keys.D7 -> transact (fun _ -> numberInput.Value <- 7::numberInput.Value)
        | Keys.D8 -> transact (fun _ -> numberInput.Value <- 8::numberInput.Value)
        | Keys.D9 -> transact (fun _ -> numberInput.Value <- 9::numberInput.Value)
        | Keys.Enter -> transact (fun _ -> desiredLevel.Value <- numberInputDisplay |> AVal.force |> clamp 0 maxLvl; numberInput.Value <- [])
        | Keys.Back -> transact (fun _ -> numberInput.Value <- match numberInput.Value with [] -> [] | _::t -> t)
        | _ -> ()
    )

    let font = Aardvark.Rendering.Text.Font("Consolas")
    let textSg =
        let t = AVal.map3 (fun sl ni dl -> sprintf "run(SPACE)\nstartLevel(O/P)=%d\ndesiredLevel=%d\ninput desired level(DIGITS+ENTER):%d" sl dl ni) startLevel numberInputDisplay desiredLevel
        Sg.text font C4b.White t
        |> Sg.scale 0.025
        |> Sg.transform (Trafo3d.Translation(-0.98,-0.85,0.0))


    let finalSg = Sg.ofList [sg;textSg]
    let task =
        app.Runtime.CompileRender(win.FramebufferSignature, finalSg)

    win.RenderTask <- task
    win.Run()
    0
