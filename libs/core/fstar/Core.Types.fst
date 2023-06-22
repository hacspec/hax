module Core.Types

unfold type u8 = FStar.UInt8.t
unfold type u32 = FStar.UInt32.t
unfold type usize = FStar.SizeT.t
type slice t = s: FStar.Seq.seq t {SizeT.fits (FStar.Seq.length s)}
type array t (l: usize) = 
  s: FStar.Seq.seq t {
       FStar.Seq.length s == FStar.SizeT.v l
    }

class index self idx = {
  output: Type;
  in_range: self -> idx -> bool;
  (.[]): s:self -> i:idx {in_range s i} -> output;
}

class update_at self idx = {
  super_index: index self idx;
  (.[]<-): s: self -> i: idx {super_index.in_range s i} -> super_index.output -> self;
}

