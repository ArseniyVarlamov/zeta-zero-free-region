#!/usr/bin/env python3
"""Complete rational/Arb certificate, including the union of all height bands."""
import json,sys,time,resource
from pathlib import Path
from fractions import Fraction
from flint import arb,fmpq,ctx
from verify_band import verify_band
ctx.prec=160

def require(name,condition,value=None):
    if not condition:raise AssertionError(f"FAILED: {name}: {value}")

def rat(s):
    x=Fraction(str(s));return fmpq(x.numerator,x.denominator)

start=time.monotonic()
config=json.loads(Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('parameters.json')).read_text())
bands=config.get('bands',[config])
R=rat(config['R'])
require('target improvement',4<R<rat('4.85025'))
require('nonempty band list',len(bands)>0)
require('first band covers log H',arb(rat(bands[0].get('Llo','28.7296')))<(arb(3)*10**12).log())
require('Yang crossover',arb(rat(bands[-1]['Lhi'])).log()/arb('21.233')>1/arb(R))
for i,cfg in enumerate(bands):
    require(f'band {i} uses claimed R',rat(cfg['R'])==R)
    require(f'band {i} nonempty',rat(cfg.get('Llo','28.7296'))<rat(cfg['Lhi']))
    if i:require(f'band {i} joins preceding band',rat(bands[i-1]['Lhi'])==rat(cfg['Llo']))
results=[];margins=[]
for cfg in bands:
    res,mm=verify_band(cfg);results.append(res);margins.append(mm)
margin=min(margins)
require('all bands positive with safety margin',margin>arb('1e-6'),margin)
print(json.dumps({'status':'PASS','statement':'C_8a <= '+config['R'],'arithmetic':'FLINT/Arb 160-bit balls and exact rational polynomials','margin':str(margin),'band_count':len(bands),'bands':results,'seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)},indent=2))
