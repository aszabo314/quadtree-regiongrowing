open System
open Aardvark.Base
open Aardvark.Rendering
open Aardvark.SceneGraph
open Aardvark.Application
open Aardvark.Application.Slim
open FSharp.Data.Adaptive
open System.Collections.Generic
open System.Threading
let mutable ct = 0
let idx() = 
    let res = ct
    ct <- ct+1
    res

type Dir = Left | Up | Right | Down

type NodeData =
    {
        idx : int
        density : float
        mutable parent : Option<QuadTree>
        location : list<int>
        level : int
    }

and QuadTree =
| Node of NodeData*bl:QuadTree*tl:QuadTree*tr:QuadTree*br:QuadTree
| Leaf of NodeData

type Traversed =
    {
        startIdx : int
        visited : MapExt<int,bool>
    }

module Traversed =
    let Empty = 
        {
            startIdx = -1
            visited = MapExt.empty
        }

module QuadTree =
    let getData (q : QuadTree) =
        match q with 
        | Leaf d -> d
        | Node (d,_,_,_,_) -> d

    let generate leafThreshold =
        ct <- 0
        let rand = RandomSystem()
        let randBetween mi ma = rand.UniformDouble() * (ma-mi) + mi
        let lvl0Density = 1.0
        let rec build (locationCode : list<int>) (density : float) (level : int) =
            if density <= leafThreshold then Leaf {idx = idx(); density = density; parent = None; location = locationCode; level = level}
            else
                let parts = Array.init 4 (fun _ -> randBetween 0.0 density) |> Array.sort
                let bl = build (2::locationCode) parts.[0] (level+1)
                let tl = build (0::locationCode) (parts.[1]-parts.[0]) (level+1)
                let tr = build (1::locationCode) (parts.[2]-parts.[1]) (level+1)
                let br = build (3::locationCode) (parts.[3]-parts.[2]) (level+1)
                Node({idx = idx(); density = density; parent = None; location = locationCode; level = level}, bl, tl, tr, br)
        let rec fixParents (p : Option<QuadTree>) (q : QuadTree) =
            match q with 
            | Leaf d -> d.parent <- p
            | Node (d, bl, tl, tr, br) -> 
                d.parent <- p
                fixParents (Some q) bl
                fixParents (Some q) tl
                fixParents (Some q) tr
                fixParents (Some q) br

        let res = build [] lvl0Density 0
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
                pos, posred d, posylo d
            | Node (d, bl, tl, tr, br) -> 
                let r = ma-mi
                let p00 = mi
                let p01 = V2d(mi.X + r.X/2.0, mi.Y)
                let p02 = V2d(ma.X,           mi.Y)
                let p10 = V2d(mi.X,           mi.Y + r.Y/2.0)
                let p11 = V2d(mi.X + r.X/2.0, mi.Y + r.Y/2.0)
                let p12 = V2d(ma.X,           mi.Y + r.Y/2.0)
                let p20 = V2d(mi.X,           ma.Y)
                let p21 = V2d(mi.X + r.X/2.0, ma.Y)
                let p22 = ma
                let (pa0,pr0,py0) = traverse p00 p11 tl t
                let (pa1,pr1,py1) = traverse p10 p21 tr t
                let (pa2,pr2,py2) = traverse p01 p12 bl t
                let (pa3,pr3,py3) = traverse p11 p22 br t

                Array.concat [pa0;pa1;pa2;pa3], 
                Array.concat [pr0;pr1;pr2;pr3;posred d],
                Array.concat [py0;py1;py2;py3;posylo d]
        let positions mi ma q t =
            let res = traverse mi ma q t
            res

        let ps = AVal.map2 (fun q t -> positions V2d.NN V2d.II q t) quad traversal

        let whiteBoxes = ps |> AVal.map (fun (d,_,_) -> d)
        let redTris =    ps |> AVal.map (fun (_,d,_) -> d)
        let yloTris =    ps |> AVal.map (fun (_,_,d) -> d)

        let pass0 = RenderPass.main
        let pass1 = RenderPass.after "asdasd" RenderPassOrder.Arbitrary RenderPass.main
        let pass2 = RenderPass.after "asdasd21354235" RenderPassOrder.Arbitrary pass1

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
            
        Sg.ofList [whiteSg;redSg;yloSg]

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
        let l = clamp 0 (ct-1) l
        let rec traverse (i : int) (q : QuadTree) =
            match q with 
            | Leaf _ -> 
                if i = 0 then [q] else []
            | Node (_,bl,tl,tr,br) -> 
                if i = 0 then [bl;tl;tr;br] else
                    List.concat [
                        traverse (i-1) bl
                        traverse (i-1) tl
                        traverse (i-1) tr
                        traverse (i-1) br
                    ]
        traverse l q

    let rec containsPath (outer : list<int>) (inner : list<int>) = 
        match outer,inner with 
        | [], [] -> false
        | [], _ -> true
        | _, [] -> false
        | o::router, i::rinner -> 
            (o=i)&&(containsPath router rinner)

    let contains (outer : QuadTree) (inner : QuadTree) =
        containsPath (getData outer).location (getData inner).location 

module Traversal =
    // http://web.archive.org/web/20120907211934/http://ww1.ucmss.com/books/LFS/CSREA2006/MSV4517.pdf
    let getNeighbor (d : Dir) (q : QuadTree) =
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
            constructPath (Some d) l
            |> Option.bind (fun path ->
                QuadTree.findPath path q
            )

    let regionGrowFromRandomStart (startLevel : int) (q : QuadTree) (resCb : Traversed -> unit) =
        let rand = RandomSystem()
        let startNode =
            let nodes = QuadTree.nodesOfLevel startLevel q |> List.toArray
            nodes.[rand.UniformInt(nodes.Length-1)]
        let mutable finished = MapExt.empty

        let queue = Queue<QuadTree>()
        let tryEnqueue (q : QuadTree) =
            if not (finished |> MapExt.containsKey (QuadTree.getData q).idx) then queue.Enqueue q

        tryEnqueue startNode
        
        let rec tryEnqueueNeighbor (d : Dir) (q : QuadTree) =
            match getNeighbor d q with 
            | Some n -> tryEnqueue n
            | None -> 
                match (QuadTree.getData q).parent with 
                | Some p -> tryEnqueueNeighbor d p
                | None -> ()

        while not (queue.IsEmpty()) do
            Thread.Sleep 150
            match queue.TryDequeue() with
            | (true,q) -> 
                let mutable skip = false
                if (QuadTree.getData q).level < startLevel then 
                    match q with 
                    | Leaf _ -> ()
                    | Node (_,bl,tl,tr,br) -> 
                        tryEnqueue bl
                        tryEnqueue tl
                        tryEnqueue tr
                        tryEnqueue br
                        skip <- true

                if not skip then 
                    finished <- finished |> MapExt.add (QuadTree.getData q).idx true

                    tryEnqueueNeighbor Left q
                    tryEnqueueNeighbor Up q
                    tryEnqueueNeighbor Right q
                    tryEnqueueNeighbor Down q
                resCb {startIdx = (QuadTree.getData startNode).idx; visited = finished}
            | _ -> ()
        resCb {startIdx = (QuadTree.getData startNode).idx; visited = finished}

[<EntryPoint;STAThread>]
let main argv = 
    let mutable ver = 0
    let create() =
        Log.startTimed "generate ..."    
        let res = QuadTree.generate 0.001
        ver <- ver+1
        Log.stop()
        res
    let q = AVal.init (create())

    Aardvark.Init()

    let traversed = cval Traversed.Empty

    let doIt = 
        async {
            do! Async.SwitchToNewThread()
            let mutable lastVer = ver
            while true do 
                do! Async.Sleep 50
                if lastVer <> ver then 
                    lastVer <- ver 
                    Traversal.regionGrowFromRandomStart 1 (q |> AVal.force) (fun t -> transact (fun _ -> traversed.Value <- t))
        } |> Async.Start

    let sg = QuadTree.toSg q traversed

    use app = new OpenGlApplication()
    use win = app.CreateGameWindow(4)
    
    win.Keyboard.DownWithRepeats.Values.Add (fun k -> 
        match k with 
        | Keys.Space -> transact (fun _ -> q.Value <- create())
        | _ -> ()
    )

    let task =
        app.Runtime.CompileRender(win.FramebufferSignature, sg)

    win.RenderTask <- task
    win.Run()
    0
