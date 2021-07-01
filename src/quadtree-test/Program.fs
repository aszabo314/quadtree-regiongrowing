open System
open Aardvark.Base
open Aardvark.Rendering
open Aardvark.SceneGraph
open Aardvark.Application
open Aardvark.Application.Slim
open FSharp.Data.Adaptive

type NodeData =
    {
        density : float
        mutable parent : Option<QuadTree>
    }

and QuadTree =
| Node of NodeData*bl:QuadTree*tl:QuadTree*tr:QuadTree*br:QuadTree
| Leaf of NodeData

module QuadTree =
    let rec getDensity (q : QuadTree) =
        match q with 
        | Leaf {density = d} -> d
        | Node({density = d},bl,tl,tr,br) -> d

    let rec getLevel (q : QuadTree) =
        let p = 
            match q with 
            | Leaf {parent = p} -> p
            | Node({parent = p},_,_,_,_) -> p
        
        match p with 
        | None -> 0
        | Some p -> getLevel p + 1

    let generate() =
        let rand = RandomSystem()
        let randBetween mi ma = rand.UniformDouble() * (ma-mi) + mi
        let lvl0Density = 1.0
        let leafThreshold = 0.0001
        let rec build (density : float) =
            if density <= leafThreshold then Leaf {density = density; parent = None}
            else
                let parts = Array.init 4 (fun _ -> randBetween 0.0 density) |> Array.sort
                let bl = build parts.[0]
                let tl = build (parts.[1]-parts.[0])
                let tr = build (parts.[2]-parts.[1])
                let br = build (parts.[3]-parts.[2])
                Node({density = density; parent = None}, bl, tl, tr, br)
        let rec fixParents (p : Option<QuadTree>) (q : QuadTree) =
            match q with 
            | Leaf d -> d.parent <- p
            | Node (d, bl, tl, tr, br) -> 
                d.parent <- p
                fixParents (Some q) bl
                fixParents (Some q) tl
                fixParents (Some q) tr
                fixParents (Some q) br

        let res = build lvl0Density
        fixParents None res
        res

    let toSg (quad : aval<QuadTree>) =
        let rec traverse (mi : V2d) (ma : V2d) (q : QuadTree) =
            match q with 
            | Leaf d -> 
                let pos = [|V2d(mi.X,mi.Y);V2d(mi.X,ma.Y);
                  V2d(mi.X,ma.Y);V2d(ma.X,ma.Y);
                  V2d(ma.X,ma.Y);V2d(ma.X,mi.Y);
                  V2d(ma.X,mi.Y);V2d(mi.X,mi.Y);
                |]
                pos
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
                Array.concat [
                    traverse p00 p11 tl
                    traverse p10 p21 tr
                    traverse p01 p12 bl
                    traverse p11 p22 br
                ]
        let positions mi ma q =
            Log.start "to Sg ..."
            let res = traverse mi ma q
            Log.stop() 
            res

        let ps = quad |> AVal.map (positions V2d.NN V2d.II)

        Sg.draw IndexedGeometryMode.LineList
        |> Sg.vertexAttribute DefaultSemantic.Positions ps
        |> Sg.shader {
            do! DefaultSurfaces.constantColor C4f.White
            do! DefaultSurfaces.thickLine
        }
        |> Sg.uniform "LineWidth" (AVal.constant 0.5)

[<EntryPoint;STAThread>]
let main argv = 
    let create() =
        Log.startTimed "generate ..."    
        let res = QuadTree.generate()
        Log.stop()
        res
    let q = AVal.init (create())

    Aardvark.Init()

    let sg = QuadTree.toSg q

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
