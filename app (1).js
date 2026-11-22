(function(){
"use strict";
/* ---------- helpers ---------- */
var esc=function(s){return String(s).replace(/[&<>"]/g,function(c){return{'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]})};
var lc=function(s){return s.toLowerCase()}, cap=function(s){return s?s.charAt(0).toUpperCase()+s.slice(1):s};
var rnd=function(n){return Math.floor(Math.random()*n)}, pick=function(a){return a[rnd(a.length)]};
var shuffle=function(a){a=a.slice();for(var i=a.length-1;i>0;i--){var j=rnd(i+1);var t=a[i];a[i]=a[j];a[j]=t}return a};
var trim=function(s,n){return s.length>n?s.slice(0,n-1).replace(/[ ,;/]+\S*$/,'')+'…':s};
var today=function(){var d=new Date();return Math.floor((d.getTime()-d.getTimezoneOffset()*6e4)/864e5)};
var LS={get:function(k,d){try{var v=localStorage.getItem(k);return v?JSON.parse(v):d}catch(e){return d}},set:function(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}};

/* ---------- state ---------- */
var S=LS.get('vf1',null)||{cards:{},log:{},streak:0,last:0,q:0,c:0,newPer:10};
S.cards=S.cards||{};S.log=S.log||{};S.newPer=S.newPer||10;S.mocks=S.mocks||[];
var save=function(){LS.set('vf1',S)};
var INT=[0,1,3,7,14,30];

/* ---------- cards ---------- */
var DECKS={
  syn:{name:'Synonyms',sub:'Words with close meanings'},
  ant:{name:'Antonyms',sub:'Words with opposite meanings'},
  root:{name:'Root Words',sub:'Decode unseen words from their roots'},
  conf:{name:'Confused Words',sub:'Look-alike pairs and sets'},
  idi:{name:'Idioms',sub:'From the synonym chapters'}
};
var ORDER=['syn','ant','root','conf','idi'];
var GT=(typeof GRAM!=='undefined'&&GRAM.topics)?GRAM.topics:[];
var GORDER=GT.map(function(t){return 'g:'+t.slug});
GT.forEach(function(t){DECKS['g:'+t.slug]={name:t.topic,sub:'Grammar'}});
if(GT.length)DECKS.grammar={name:'Grammar, all topics',sub:''};
var RT=(typeof RULES!=='undefined'&&RULES.topics)?RULES.topics:[];
var RORDER=RT.map(function(t){return 'rl:'+t.slug});
RT.forEach(function(t){DECKS['rl:'+t.slug]={name:t.topic,sub:'120 Rules'}});
if(RT.length)DECKS.rules120={name:'120 Grammar Rules, all',sub:''};
var ALLDECKS=ORDER.concat(GORDER).concat(RORDER);
var CAT={syn:'Synonyms',ant:'Antonyms',root:'Root words',conf:'Confused words',idi:'Idioms'};
var isG=function(d){return d.charAt(0)==='g'&&d.charAt(1)===':'};
var isR=function(d){return d.slice(0,3)==='rl:'};
var hash=function(s){var h=5381;for(var i=0;i<s.length;i++)h=((h<<5)+h+s.charCodeAt(i))|0;return (h>>>0).toString(36)};
var CARDS=[],byId={};
function addCard(c){if(!byId[c.id]){byId[c.id]=c;CARDS.push(c)}}
DATA.words.forEach(function(w){if(w.syn.length>=2)addCard({id:'w:'+w.w,deck:'syn',w:w});if(w.ant.length>=2)addCard({id:'a:'+w.w,deck:'ant',w:w})});
DATA.roots.forEach(function(r){r.words.forEach(function(x){addCard({id:'r:'+x.w,deck:'root',x:x,r:r})})});
DATA.conf.forEach(function(g,i){addCard({id:'c:'+i,deck:'conf',g:g})});
DATA.words.forEach(function(w){w.idioms.forEach(function(it){addCard({id:'i:'+it.t,deck:'idi',it:it,from:w.w})})});
GT.forEach(function(t){t.cards.forEach(function(k){addCard({id:'g:'+t.slug+':'+hash(k.q),deck:'g:'+t.slug,k:k,topic:t.topic})})});
var GQ=[];GT.forEach(function(t){t.questions.forEach(function(q){GQ.push({t:t,q:q})})});
RT.forEach(function(t){t.cards.forEach(function(k){addCard({id:'rl:'+t.slug+':'+hash(k.q),deck:'rl:'+t.slug,k:k,topic:t.topic})})});
var RQ=[];RT.forEach(function(t){t.questions.forEach(function(q){RQ.push({t:t,q:q})})});
var LIB=CARDS.filter(function(c){return c.deck!=='ant'});
var POOL=[];(function(){var s={};DATA.words.forEach(function(w){w.syn.concat(w.ant).forEach(function(x){var k=lc(x);if(!s[k]){s[k]=1;POOL.push(x)}})})})();
var ROOTWORDS=[];DATA.roots.forEach(function(r){r.words.forEach(function(x){ROOTWORDS.push({x:x,r:r})})});

/* ---------- spaced repetition ---------- */
function logDay(k,n){var t=today();S.log[t]=S.log[t]||{r:0,q:0};S.log[t][k]+=n||1;
  if(S.last!==t){S.streak=(S.last===t-1)?S.streak+1:1;S.last=t}}
function grade(id,know){var t=today(),c=S.cards[id]||{b:0,d:t,s:0};c.s++;
  if(know){c.b=Math.min(5,c.b+1);c.d=t+INT[c.b]}else{c.b=0;c.d=t}
  S.cards[id]=c;logDay('r');save()}
function penalize(id){var t=today(),c=S.cards[id]||{b:0,d:t,s:0};c.b=0;c.d=t;c.s=Math.max(1,c.s);S.cards[id]=c}
function inDeck(c,deck){return deck==='all'||c.deck===deck||(deck==='vocab'&&!isG(c.deck)&&!isR(c.deck))||(deck==='grammar'&&isG(c.deck))||(deck==='rules120'&&isR(c.deck))}
function decksOf(deck){return deck==='all'?ALLDECKS:deck==='vocab'?ORDER:deck==='grammar'?GORDER:deck==='rules120'?RORDER:[deck]}
function counts(deck){var t=today(),p=CARDS.filter(function(c){return inDeck(c,deck)});
  var due=0,fresh=0,seen=0,mast=0;p.forEach(function(c){var s=S.cards[c.id];if(!s)fresh++;else{seen++;if(s.d<=t)due++;if(s.b>=4)mast++}});
  return{total:p.length,due:due,fresh:fresh,seen:seen,mast:mast}}
function rr(lists,lim){var out=[],i=0;while(out.length<lim&&lists.some(function(f){return f.length>i})){lists.forEach(function(f){if(f[i]&&out.length<lim)out.push(f[i])});i++}return out}
var SETN=10;
function setInfo(d){var p=CARDS.filter(function(c){return c.deck===d}),sets=Math.ceil(p.length/SETN),cur=sets,cf=[],seen=0;
  p.forEach(function(c){if(S.cards[c.id])seen++});
  for(var i=0;i<sets;i++){var u=p.slice(i*SETN,i*SETN+SETN).filter(function(c){return !S.cards[c.id]});if(u.length){cur=i;cf=u;break}}
  return{total:p.length,sets:sets,cur:cur,curFresh:cf,seen:seen}}
function gFresh(){var ds=GORDER.map(setInfo).filter(function(x){return x.cur<x.sets}),st=ds.filter(function(x){return x.seen>0});
  return(st.length?st:ds.slice(0,1)).map(function(x){return x.curFresh})}
function rFresh(){var ds=RORDER.map(setInfo).filter(function(x){return x.cur<x.sets}),st=ds.filter(function(x){return x.seen>0});
  return(st.length?st:ds.slice(0,1)).map(function(x){return x.curFresh})}
function buildQueue(deck){var t=today(),decks=decksOf(deck),due=[],fresh=[];
  decks.forEach(function(d){var p=CARDS.filter(function(c){return c.deck===d});
    p.forEach(function(c){var s=S.cards[c.id];if(s&&s.d<=t)due.push(c)});
    if(!isG(d)&&!isR(d))fresh.push(p.filter(function(c){return !S.cards[c.id]}))});
  var gf=(deck==='all'||deck==='grammar')?gFresh():(isG(deck)?[setInfo(deck).curFresh]:[]);
  var rf=(deck==='all'||deck==='rules120')?rFresh():(isR(deck)?[setInfo(deck).curFresh]:[]);
  var nw=[],lim=S.newPer;
  if(deck==='all'){var a=rr(fresh,lim),b=rr(shuffle(gf),lim),c3=rr(shuffle(rf),lim);
    for(var k=0;nw.length<lim&&(k<a.length||k<b.length||k<c3.length);k++){if(a[k]&&nw.length<lim)nw.push(a[k]);if(b[k]&&nw.length<lim)nw.push(b[k]);if(c3[k]&&nw.length<lim)nw.push(c3[k])}}
  else nw=rr(fresh.concat(gf).concat(rf),lim);
  return shuffle(due).concat(nw)}

/* ---------- card faces ---------- */
function chips(a,cls){return '<div class="chips">'+a.map(function(x){return '<span class="chip '+(cls||'')+'">'+esc(cap(x))+'</span>'}).join('')+'</div>'}
var br=function(s){return esc(s).replace(/\n/g,'<br>')};
function front(c){
  if(isG(c.deck)||isR(c.deck))return '<div class="mono">'+esc(c.topic)+(c.k.tag?' · '+esc(c.k.tag):'')+'</div><div class="q" style="margin-top:12px">'+esc(c.k.q)+'</div><p class="hint">Answer from memory, then tap to check.</p>';
  if(c.deck==='syn')return '<div class="mono">'+esc(c.w.pos||'word')+'</div><div class="word"><span>'+esc(c.w.w)+'</span></div><p class="hint">Recall three synonyms, then tap to check.</p>';
  if(c.deck==='ant')return '<div class="mono">'+esc(c.w.pos||'word')+' · opposites</div><div class="word"><span>'+esc(c.w.w)+'</span></div><p class="hint">Recall three antonyms, then tap to check.</p>';
  if(c.deck==='root')return '<div class="mono">Root '+esc(c.r.root)+' · '+esc(c.r.meaning||'')+'</div><div class="word"><span>'+esc(c.x.w)+'</span></div><p class="hint">'+esc(c.x.pos)+' · say the meaning in your own words, then tap.</p>';
  if(c.deck==='conf')return '<div class="mono">Confused set</div><div class="word" style="font-size:clamp(26px,7vw,36px)">'+c.g.items.map(function(i){return '<div><span>'+esc(i.w)+'</span></div>'}).join('')+'</div><p class="hint">Give each word its own meaning, then tap.</p>';
  return '<div class="mono">Idiom</div><div class="word" style="font-size:clamp(28px,8vw,40px)"><span>'+esc(c.it.t)+'</span></div><p class="hint">What does it mean? Tap to check.</p>'}
function back(c,full){
  if(isG(c.deck)||isR(c.deck))return '<div class="mono">'+esc(c.topic)+(c.k.tag?' · '+esc(c.k.tag):'')+'</div><div class="q" style="font-size:18px;margin-top:10px">'+esc(c.k.q)+'</div><p style="font-size:17px;margin-top:12px">'+br(c.k.a)+'</p>';
  if(c.deck==='syn'){var w=c.w,h='';
    h+='<div class="mono">'+esc(w.w)+(w.pos?' · '+esc(w.pos):'')+'</div>';
    h+='<div class="mono lab">Synonyms</div>'+chips(w.syn.slice(0,8),'mk')+(w.syn.length>8?'<details><summary>More synonyms <small>'+(w.syn.length-8)+'</small></summary>'+chips(w.syn.slice(8))+'</details>':'');
    if(full&&w.ant.length)h+='<div class="mono lab">Antonyms</div>'+chips(w.ant.slice(0,8),'ant')+(w.ant.length>8?'<details><summary>More antonyms <small>'+(w.ant.length-8)+'</small></summary>'+chips(w.ant.slice(8),'ant')+'</details>':'');
    if(w.idioms.length)h+='<div class="mono lab">Idioms</div><ul>'+w.idioms.map(function(i){return '<li><b>'+esc(i.t)+'</b>: '+esc(i.m)+'</li>'}).join('')+'</ul>';
    return h}
  if(c.deck==='ant'){var w2=c.w;
    return '<div class="mono">'+esc(w2.w)+(w2.pos?' · '+esc(w2.pos):'')+'</div><div class="mono lab">Antonyms</div>'+chips(w2.ant.slice(0,8),'mk')+(w2.ant.length>8?'<details><summary>More antonyms <small>'+(w2.ant.length-8)+'</small></summary>'+chips(w2.ant.slice(8))+'</details>':'')+(w2.syn.length?'<div class="mono lab">For contrast, synonyms</div>'+chips(w2.syn.slice(0,5),'ant'):'')}
  if(c.deck==='root'){var fam=c.r.words.filter(function(x){return x!==c.x}).map(function(x){return x.w});
    return '<div class="mono">'+esc(c.x.pos)+'</div><div class="word" style="font-size:28px"><span>'+esc(c.x.w)+'</span></div><p style="font-size:18px;margin-top:12px">'+esc(c.x.m)+'</p><div class="mono lab">Root '+esc(c.r.root)+' · '+esc(c.r.meaning||'')+'</div>'+chips(fam.slice(0,12))}
  if(c.deck==='conf')return c.g.items.map(function(i){return '<p><b>'+esc(i.w)+'</b> <span class="muted">('+esc(i.pos)+')</span><br>'+esc(i.m)+'</p>'}).join('')+(c.g.ex.length?'<div class="mono lab">Examples</div><ul>'+c.g.ex.map(function(e){return '<li>'+esc(e)+'</li>'}).join('')+'</ul>':'');
  return '<div class="mono">Idiom</div><div class="word" style="font-size:26px"><span>'+esc(c.it.t)+'</span></div><p style="font-size:18px;margin-top:12px">'+esc(c.it.m)+'</p>'+(c.from?'<p class="muted small">From the '+esc(c.from)+' chapter</p>':'')}

/* ---------- quiz generation ---------- */
function infl(w){w=lc(w);var b=w.replace(/e$/,''),y=w.replace(/y$/,'i');return[w,w+'s',w+'es',w+'d',w+'ed',w+'ing',b+'ing',b+'ed',y+'es',w.replace(/y$/,'ied')]}
function uniq(a){var s={};return a.filter(function(x){var k=lc(x);if(s[k])return false;s[k]=1;return true})}
function fillOpts(correct,exclude,source,n){var ex={};exclude.forEach(function(x){ex[lc(x)]=1});var out=[correct];ex[lc(correct)]=1;var tries=0;
  while(out.length<n&&tries++<200){var c=pick(source);if(!ex[lc(c)]){ex[lc(c)]=1;out.push(c)}}return out}
function mk(prompt,sub,opts,ans,explain,id,tag){var o=shuffle(opts);return{prompt:prompt,sub:sub,opts:o,ans:o.indexOf(ans),explain:explain,id:id,tag:tag}}
function qSynAnt(c,kind){var w=c.w,good=kind==='syn'?w.syn:w.ant,bad=kind==='syn'?w.ant:w.syn;if(good.length<1)return null;
  var gl=good.map(lc),correct=pick(good.slice(0,10)),ex=w.syn.concat(w.ant,[w.w]);
  var trap=bad.filter(function(x){return gl.indexOf(lc(x))<0});var opts=[correct];
  if(trap.length)opts.push(pick(trap));
  while(opts.length<4){var p=fillOpts(pick(POOL),ex.concat(opts),POOL,1)[0];if(opts.map(lc).indexOf(lc(p))<0&&ex.map(lc).indexOf(lc(p))<0)opts.push(p)}
  opts=opts.map(cap);
  return mk(kind==='syn'?'Closest in meaning to':'Opposite in meaning to',w.w,opts,cap(correct),
    '<b>'+esc(w.w)+'</b><br>Synonyms: '+esc(good===w.syn?w.syn.slice(0,8).join(', '):w.syn.slice(0,8).join(', '))+(w.ant.length?'<br>Antonyms: '+esc(w.ant.slice(0,8).join(', ')):''),c.id,'syn')}
function qRoot(c,kind){var x=c.x,r=c.r;
  if(kind==='mean'){var others=ROOTWORDS.filter(function(o){return o.r!==r}).map(function(o){return trim(o.x.m,70)});
    var corr=trim(x.m,70),opts=fillOpts(corr,[],others,4);return mk('What does this word mean?',x.w,opts,corr,'<b>'+esc(x.w)+'</b>: '+esc(x.m)+'<br>Root '+esc(r.root)+' ('+esc(r.meaning||'')+')',c.id,'root')}
  if(kind==='word'){var ow=ROOTWORDS.filter(function(o){return o.r!==r}).map(function(o){return o.x.w});
    var opts=fillOpts(x.w,[],ow,4);return mk('Which word fits this meaning?',trim(x.m,110),opts,x.w,'<b>'+esc(x.w)+'</b> comes from root '+esc(r.root)+' ('+esc(r.meaning||'')+')',c.id,'root')}
  var STOP=['to','of','the','a','and','or'],tk=function(x){return lc(x).split(/[^a-z]+/).filter(function(t){return t&&STOP.indexOf(t)<0})},rt=tk(r.meaning||'');var om=DATA.roots.filter(function(o){return o!==r&&o.meaning&&!tk(o.meaning).some(function(t){return rt.indexOf(t)>=0})}).map(function(o){return o.meaning});if(!r.meaning)return null;
  var opts=fillOpts(r.meaning,[],om,4);return mk('The root below means',r.root,opts,r.meaning,'Words: '+esc(r.words.slice(0,8).map(function(w){return w.w}).join(', ')),c.id,'root')}
var CONFW=[];DATA.conf.forEach(function(g,i){g.items.forEach(function(it){CONFW.push({w:it.w,pos:it.pos,g:i})})});
function confOpts(g){var base=g.items.map(function(i){return i.w}),gi=DATA.conf.indexOf(g),have={};base.forEach(function(w){have[lc(w)]=1});
  var pos=g.items[0].pos,same=CONFW.filter(function(c){return c.g!==gi&&c.pos===pos}),any=CONFW.filter(function(c){return c.g!==gi});
  var out=base.slice(),src=shuffle(same).concat(shuffle(any)),k=0;
  while(out.length<4&&k<src.length){var w=src[k++].w;if(!have[lc(w)]){have[lc(w)]=1;out.push(w)}}return out}
function qConf(c,kind){var g=c.g;
  if(kind==='blank'){var cands=[];g.ex.forEach(function(s){var toks=s.match(/[A-Za-z']+/g)||[],hit=[];
      g.items.forEach(function(it,ix){toks.forEach(function(t){if(infl(it.w).indexOf(lc(t))>=0)hit.push({ix:ix,t:t})})});
      if(hit.length===1)cands.push({s:s,h:hit[0]})});
    if(!cands.length)return null;var cd=pick(cands);var sent=cd.s.replace(new RegExp('\\b'+cd.h.t+'\\b'),'_____');
    var words=confOpts(g);
    return mk('Fill in the blank',sent,words,g.items[cd.h.ix].w,g.items.map(function(i){return '<b>'+esc(i.w)+'</b>: '+esc(i.m)}).join('<br>'),c.id,'conf')}
  var it=pick(g.items);return mk('Which word matches this meaning?',trim(it.m,120),confOpts(g),it.w,g.items.map(function(i){return '<b>'+esc(i.w)+'</b>: '+esc(i.m)}).join('<br>'),c.id,'conf')}
var IDI=CARDS.filter(function(c){return c.deck==='idi'});
function qIdi(c){var oth=IDI.filter(function(o){return o!==c}).map(function(o){return trim(o.it.m,70)});if(oth.length<3)return null;
  var corr=trim(c.it.m,70);return mk('What does this idiom mean?',c.it.t,fillOpts(corr,[],oth,4),corr,'<b>'+esc(c.it.t)+'</b>: '+esc(c.it.m),c.id,'idi')}
function makeQ(c){var q=null,t=0;
  while(!q&&t++<8){
    if(c.deck==='syn')q=qSynAnt(c,'syn');
    else if(c.deck==='ant')q=qSynAnt(c,'ant');
    else if(c.deck==='root')q=qRoot(c,pick(['mean','mean','word','root']));
    else if(c.deck==='conf')q=qConf(c,Math.random()<.65?'blank':'mean');
    else if(c.deck==='idi')q=qIdi(c);
    else return null}
  if(q)q.cat=CAT[c.deck];return q}
function gq(g){var q=g.q,e=q.type==='err';
  return{prompt:e?'Find the part with the error (D means no error)':'Choose the best option',sub:q.stem,opts:q.opts.slice(),ans:q.ans,
    explain:(q.exp?esc(q.exp):'')+'<br><span class="muted">'+esc(g.t.topic)+'</span>',id:null,tag:'gram',cat:e?'Error spotting':'Grammar MCQ',long:true}}
function vocabQuiz(deck,n){var pool=CARDS.filter(function(c){return !isG(c.deck)&&(deck==='all'||deck==='vocab'||c.deck===deck)});
  if(deck==='all'||deck==='vocab'){var per=ORDER.map(function(d){return shuffle(pool.filter(function(c){return c.deck===d}))});
    pool=[];var i=0;while(pool.length<n*3&&per.some(function(p){return p.length>i})){per.forEach(function(p){if(p[i])pool.push(p[i])});i++}pool=shuffle(pool)}
  else{var t=today();pool=shuffle(pool).sort(function(a,b){var sa=S.cards[a.id],sb=S.cards[b.id];return((sa&&sa.d<=t)?0:1)-((sb&&sb.d<=t)?0:1)})}
  var out=[];for(var k=0;k<pool.length&&out.length<n;k++){var q=makeQ(pool[k]);if(q)out.push(q)}return out}
function buildQuiz(deck,n){
  if(deck==='gram')return shuffle(GQ.filter(function(g){return !V.gtopic||g.t.slug===V.gtopic})).slice(0,n).map(gq);
  if(deck==='rules')return shuffle(RQ.filter(function(g){return !V.rtopic||g.t.slug===V.rtopic})).slice(0,n).map(gq);
  if(deck==='all'&&(GQ.length||RQ.length)){var gl=GQ.concat(RQ),ng=Math.round(n*.4);return shuffle(vocabQuiz('vocab',n-ng).concat(shuffle(gl).slice(0,ng).map(gq)))}
  return vocabQuiz(deck,n)}
/* ---------- SSC-style mock ---------- */
var MOCK_N=25,MOCK_MIN=15;
var MOCKSPEC=[['Error spotting',6],['Grammar MCQ',4],['Synonyms',3],['Antonyms',3],['Idioms',2],['Root words',2],['Confused words',5]];
function fromDeck(d){var cs=shuffle(CARDS.filter(function(c){return c.deck===d})),k=0;return function(){while(k<cs.length){var q=makeQ(cs[k++]);if(q)return q}return null}}
function newMock(){var gerr=shuffle(GQ.filter(function(g){return g.q.type==='err'})).map(gq),gm=shuffle(GQ.filter(function(g){return g.q.type!=='err'})).map(gq);
  var src={'Error spotting':function(){return gerr.pop()||null},'Grammar MCQ':function(){return gm.pop()||null},'Synonyms':fromDeck('syn'),'Antonyms':fromDeck('ant'),'Idioms':fromDeck('idi'),'Root words':fromDeck('root'),'Confused words':fromDeck('conf')};
  var list=[],seen={},ok=function(q){if(!q)return false;var k=q.sub+'|'+q.prompt;if(seen[k])return false;seen[k]=1;return true};
  MOCKSPEC.forEach(function(sp){for(var i=0;i<sp[1];i++){var q=src[sp[0]]();if(ok(q))list.push(q)}});
  var names=Object.keys(src),tries=0;while(list.length<MOCK_N&&tries<400){var q2=src[names[tries++%names.length]]();if(ok(q2))list.push(q2)}
  return{qs:list,i:0,a:list.map(function(){return null}),mk:list.map(function(){return false}),end:Date.now()+MOCK_MIN*60000,start:Date.now(),done:false,confirm:false,palOpen:false,only:false}}
/* ---------- views ---------- */
var app=document.getElementById('app');
var V={tab:'today',mode:null,deck:'all',gtopic:'',rtopic:'',cnt:10,timed:false,sub:null};
var L=null,Q=null,M=null,tick=null,mtick=null;
var ICON={
  today:'<svg viewBox="0 0 24 24"><rect x="3.5" y="5" width="17" height="15" rx="2.5"/><path d="M3.5 10h17M8 3v4M16 3v4"/></svg>',
  practice:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="8.5"/><circle cx="12" cy="12" r="3.5"/></svg>',
  library:'<svg viewBox="0 0 24 24"><path d="M5 4h4v16H5zM11 4h4v16h-4zM17.5 5.5l3.5 1-3.5 13.5-3.5-1z"/></svg>',
  mock:'<svg viewBox="0 0 24 24"><circle cx="12" cy="13" r="8"/><path d="M12 9v4l2.5 2M9.5 3h5"/></svg>',
  stats:'<svg viewBox="0 0 24 24"><path d="M5 20V11M12 20V5M19 20v-7"/></svg>'};
function tabs(){return '<nav class="tabs" aria-label="Sections"><div>'+[['today','Today'],['practice','Practice'],['mock','Mock'],['library','Library'],['stats','Progress']].map(function(t){
  return '<button class="tab" data-tab="'+t[0]+'" aria-current="'+(V.tab===t[0])+'">'+ICON[t[0]]+t[1]+'</button>'}).join('')+'</div></nav>'}
function topbar(){var t=today(),l=S.log[t]||{r:0,q:0},streak=(S.last===t||S.last===t-1)?S.streak:0;
  return '<div class="top"><div class="brand"><span>Crack</span>Vocab</div><div class="pills"><span class="pill">'+streak+' day streak</span><span class="pill">'+(l.r+l.q)+' today</span></div></div>'}
function shell(inner,withTabs){app.innerHTML=(withTabs===false?'':topbar())+inner+(withTabs===false?'':tabs())}

function deckCard(d){var c=counts(d);
  return '<div class="card deck"><div><h3>'+DECKS[d].name+'</h3><div class="sub">'+DECKS[d].sub+'</div></div><div class="mono">'+c.total+' cards</div>'+
    '<div class="meter" role="img" aria-label="'+c.mast+' mastered, '+(c.seen-c.mast)+' learning, '+c.fresh+' new"><i class="m" style="width:'+(c.mast/c.total*100)+'%"></i><i class="s" style="width:'+((c.seen-c.mast)/c.total*100)+'%"></i></div>'+
    '<div class="sub" style="grid-column:1/-1">'+c.due+' due · '+c.fresh+' new · '+c.mast+' mastered</div>'+
    '<div class="deckbtns"><button class="btn" data-act="learn" data-deck="'+d+'">Learn</button><button class="btn" data-act="quiz" data-deck="'+d+'">Quick test</button></div></div>'}
function topicRow(d,qn){var c=counts(d),si=setInfo(d);return '<div class="gh"><div class="t"><b>'+esc(DECKS[d].name)+'</b><span class="muted small">'+(si.cur>=si.sets?'All '+si.sets+' sets done':'Set '+(si.cur+1)+' of '+si.sets)+' · '+si.seen+'/'+c.total+' started · '+c.due+' due'+(qn?' · '+qn+' questions':'')+'</span><div class="meter" role="img" aria-label="'+c.mast+' mastered, '+(c.seen-c.mast)+' learning"><i class="m" style="width:'+(c.mast/c.total*100)+'%"></i><i class="s" style="width:'+((c.seen-c.mast)/c.total*100)+'%"></i></div></div><div class="row"><button class="btn" data-act="learn" data-deck="'+d+'">Learn</button>'+(qn?'<button class="btn" data-act="quiz" data-deck="'+d+'">Test</button>':'')+'</div></div>'}
var SUBLABEL={vocab:'Vocabulary',grammar:'Grammar',rules120:'120 Grammar Rules'};
function viewToday(){
  if(V.sub)return viewTodaySub(V.sub);
  var all=counts('all'),q=buildQueue('all'),dueN=all.due,cg=counts('grammar'),cv=counts('vocab'),cr=counts('rules120');
  var h='<div class="stack"><div class="hero"><div class="mono">Today</div><h1>'+(q.length?q.length+' cards ready':'All caught up')+'</h1><p>'+
    (q.length?dueN+' due for review, '+(q.length-dueN)+' new. About '+Math.max(3,Math.round(q.length*.6))+' minutes.':'Nothing due. Take a practice test or pull in new cards below.')+'</p>'+
    '<div class="row"><button class="btn primary" data-act="learn" data-deck="all"'+(q.length?'':' disabled')+'>Mixed review (today’s session)</button></div></div>';
  h+='<button class="sech" data-act="grp" data-g="vocab"><h2><span class="chev">›</span>Vocabulary</h2><span class="mono">'+cv.mast+' / '+cv.total+' mastered</span></button>';
  if(GORDER.length)h+='<button class="sech" data-act="grp" data-g="grammar"><h2><span class="chev">›</span>Grammar</h2><span class="mono">'+cg.mast+' / '+cg.total+' mastered</span></button>';
  if(RORDER.length)h+='<button class="sech" data-act="grp" data-g="rules120"><h2><span class="chev">›</span>120 Grammar Rules</h2><span class="mono">'+cr.mast+' / '+cr.total+' mastered</span></button>';
  h+='<div class="card"><div class="row"><div class="grow"><b>New cards per session</b><div class="muted small">Review cards always come first.</div></div><div class="seg" role="group" aria-label="New cards per session">'+
    [5,10,20].map(function(n){return '<button data-new="'+n+'" aria-pressed="'+(S.newPer===n)+'">'+n+'</button>'}).join('')+'</div></div></div></div>';
  shell(h)}
function viewTodaySub(g){
  var h='<div class="row" style="justify-content:space-between;margin-bottom:10px"><button class="btn ghost" data-act="subback">‹ Back</button><span class="mono">'+SUBLABEL[g]+'</span></div>';
  if(g==='vocab'){h+=ORDER.map(function(d){return deckCard(d)}).join('')}
  else if(g==='grammar'){var qn={};GT.forEach(function(t){qn['g:'+t.slug]=t.questions.length});
    h+='<div class="card"><div class="row" style="margin-bottom:6px"><button class="btn grow" data-act="learn" data-deck="grammar">Learn grammar</button><button class="btn grow" data-act="quiz" data-deck="grammar">Test grammar</button></div>'+
      GORDER.map(function(d){return topicRow(d,qn[d])}).join('')+'</div>'}
  else if(g==='rules120'){var rn={};RT.forEach(function(t){rn['rl:'+t.slug]=t.questions.length});
    h+='<div class="card"><div class="row" style="margin-bottom:6px"><button class="btn grow" data-act="learn" data-deck="rules120">Learn all rules</button><button class="btn grow" data-act="quiz" data-deck="rules120">Test all rules</button></div>'+
      RORDER.map(function(d){return topicRow(d,rn[d])}).join('')+'</div>'}
  shell(h)}

function viewLearn(){
  if(!L||L.i>=L.q.length){return viewLearnDone()}
  var c=L.q[L.i],pct=Math.round(L.i/L.q.length*100);
  var h='<div class="row" style="justify-content:space-between;margin-bottom:10px"><button class="btn ghost" data-act="exit">Close</button><span class="mono">'+(L.i+1)+' / '+L.q.length+' · '+DECKS[c.deck].name+'</span></div>'+
    '<div class="prog" style="margin-bottom:14px"><i style="width:'+pct+'%"></i></div>'+(L.note?'<div class="fb small" style="margin:0 0 12px">'+esc(L.note)+'</div>':'')+
    '<div class="flip"'+(L.flipped?'':' data-act="flip" role="button" tabindex="0" aria-label="Reveal answer"')+'>'+(L.flipped?back(c):front(c))+(L.flipped?'':'<p class="mono" style="margin-top:22px">Tap to reveal</p>')+'</div>';
  if(L.flipped)h+='<div class="grade"><button class="btn again" data-act="again">Again</button><button class="btn know" data-act="know">Got it</button></div>';
  L.note='';shell(h,false);window.scrollTo(0,0)}
function viewLearnDone(){var n=L?L.done:0;
  shell('<div class="stack" style="margin-top:30px"><div class="card"><div class="mono">Session complete</div><div class="score">'+n+'</div><p>cards reviewed. Cards you got right come back in 1, 3, 7, 14 then 30 days. Missed ones return today.</p>'+
   '<div class="row"><button class="btn primary" data-act="quiz" data-deck="'+(L?L.deck:'all')+'">Test yourself now</button><button class="btn" data-act="exit">Back to Today</button></div></div></div>',false);window.scrollTo(0,0)}

function viewPractice(){
  var decks=[['all','Mixed'],['vocab','Vocabulary']].concat(GQ.length?[['gram','Grammar']]:[]).concat(RQ.length?[['rules','120 Grammar Rules']]:[]).concat(ORDER.map(function(d){return[d,DECKS[d].name]}));
  var h='<div class="stack"><div class="sec"><h2>Practice test</h2></div><div class="card stack">'+
   '<div><div class="mono lab" style="margin-top:0">Deck</div><div class="seg" id="deckseg">'+decks.map(function(d){return '<button data-deck="'+d[0]+'" aria-pressed="'+(V.deck===d[0])+'">'+d[1]+'</button>'}).join('')+'</div></div>'+
   (V.deck==='gram'?'<div><div class="mono lab" style="margin-top:0">Grammar topic</div><select id="gtopic" aria-label="Grammar topic"><option value="">All topics ('+GQ.length+' questions)</option>'+GT.filter(function(t){return t.questions.length}).map(function(t){return '<option value="'+t.slug+'"'+(V.gtopic===t.slug?' selected':'')+'>'+esc(t.topic)+' ('+t.questions.length+')</option>'}).join('')+'</select></div>':'')+
   '<div><div class="mono lab" style="margin-top:0">Questions</div><div class="seg">'+[10,20,30].map(function(n){return '<button data-cnt="'+n+'" aria-pressed="'+(V.cnt===n)+'">'+n+'</button>'}).join('')+'</div></div>'+
   '<div><div class="mono lab" style="margin-top:0">Pace</div><div class="seg"><button data-timed="0" aria-pressed="'+(!V.timed)+'">Relaxed</button><button data-timed="1" aria-pressed="'+V.timed+'">Exam pace, 20 s each</button></div></div>'+
   '<button class="btn primary" data-act="quiz" data-deck="'+V.deck+'" style="min-height:52px;font-size:16px">Start test</button></div>'+
   '<div class="card small muted">Don\'t just practise. Dominate.<br>Challenge yourself. Learn from mistakes. Turn knowledge into mastery.<br>Your next level starts here. 🚀</div></div>';
  shell(h)}

function viewQuiz(){
  if(!Q||Q.i>=Q.list.length)return viewResult();
  var q=Q.list[Q.i],a=Q.ans;
  var h='<div class="row" style="justify-content:space-between;margin-bottom:10px"><button class="btn ghost" data-act="exit">Quit</button><span class="mono">'+(Q.i+1)+' / '+Q.list.length+' · score '+Q.score+'</span></div>'+
    '<div class="prog '+(Q.timed?'timer':'')+'" style="margin-bottom:6px"><i id="tbar" style="width:'+(Q.timed?100:Math.round(Q.i/Q.list.length*100))+'%"></i></div>'+
    '<div class="mono" style="margin-top:14px">'+esc(q.prompt)+'</div><div class="q'+((q.long||q.sub.length>70)?' long':'')+'"><em>'+esc(q.sub)+'</em></div><div class="opts">'+
    q.opts.map(function(o,i){var cls='opt'+(a!==null?(i===q.ans?' ok':(i===a?' no':'')):'');
      return '<button class="'+cls+'" data-opt="'+i+'"'+(a!==null?' disabled':'')+'><span class="bubble">'+'ABCD'.charAt(i)+'</span><span>'+esc(o)+'</span></button>'}).join('')+'</div>';
  if(a!==null)h+='<div class="fb"><b>'+(a===q.ans?(Q.retried?'Correct on retry (no extra score)':'Correct'):(a===-1?'Time up':'Not quite'))+'</b><br>'+q.explain+'</div><div class="row" style="margin-top:14px">'+(a!==q.ans?'<button class="btn grow" data-act="retryq" style="min-height:52px">Retry this question</button>':'')+'<button class="btn primary grow" data-act="next" style="min-height:52px">'+(Q.i+1>=Q.list.length?'See result':'Next')+'</button></div>';
  shell(h,false);window.scrollTo(0,0);if(a===null&&Q.timed)startTimer()}
function startTimer(){clearInterval(tick);var t0=Date.now(),lim=20000;
  tick=setInterval(function(){var el=document.getElementById('tbar');var p=1-(Date.now()-t0)/lim;if(el)el.style.width=Math.max(0,p*100)+'%';if(p<=0){clearInterval(tick);answer(-1)}},100)}
function answer(i){if(!Q||Q.ans!==null)return;clearInterval(tick);var q=Q.list[Q.i];
  if(Q.retry){Q.retry=false;Q.retried=true;Q.ans=i;return viewQuiz()}Q.ans=i;S.q++;logDay('q');
  if(i===q.ans){Q.score++;S.c++}else{Q.wrong.push(q);if(q.id)penalize(q.id)}save();viewQuiz()}
function viewResult(){var n=Q.list.length,pct=Math.round(Q.score/n*100);if(!Q.saved){Q.saved=1;S.lt=[Q.score,n];save()}
  var h='<div class="stack" style="margin-top:20px"><div class="card"><div class="mono">Result</div><div class="score">'+Q.score+'<span class="muted" style="font-size:26px"> / '+n+'</span></div><p>'+pct+'% correct. '+
    (pct>=85?'Exam-ready on this set.':pct>=60?'Solid. The misses below are queued for review.':'Run the Learn session first, then retest.')+'</p>'+
    '<div class="row"><button class="btn primary" data-act="quiz" data-deck="'+Q.deck+'">New test</button>'+(Q.wrong.length?'<button class="btn" data-act="retry">Redo the '+Q.wrong.length+' I missed</button>':'')+'<button class="btn" data-act="exit">Done</button></div></div>';
  if(Q.wrong.length)h+='<div class="card"><div class="mono" style="margin-bottom:6px">Review misses</div>'+Q.wrong.map(function(q){return '<div class="wrong"><b>'+esc(q.sub)+'</b><span class="small muted">'+esc(q.prompt)+'</span><span class="small">'+q.explain+'</span></div>'}).join('')+'</div>';
  shell(h+'</div>',false);window.scrollTo(0,0)}

var LQ='';
function entryHTML(c){return back(c,true)}
function entryTitle(c){if(isG(c.deck)||isR(c.deck))return[c.k.q,c.topic];if(c.deck==='syn')return[c.w.w,'Syn / Ant'];if(c.deck==='root')return[c.x.w,'Root '+c.r.root];
  if(c.deck==='conf')return[c.g.items.map(function(i){return i.w}).join(' / '),'Confused'];return[c.it.t,'Idiom']}
function searchText(c){if(isG(c.deck)||isR(c.deck))return(c.k.q+' '+c.k.a+' '+c.topic).toLowerCase();if(c.deck==='syn')return(c.w.w+' '+c.w.syn.join(' ')+' '+c.w.ant.join(' ')).toLowerCase();
  if(c.deck==='root')return(c.x.w+' '+c.x.m+' '+c.r.root).toLowerCase();if(c.deck==='conf')return c.g.items.map(function(i){return i.w+' '+i.m}).join(' ').toLowerCase();return(c.it.t+' '+c.it.m).toLowerCase()}
function headOf(c){return lc(entryTitle(c)[0])}
function viewLibrary(){
  var h='<div class="stack"><div class="sec"><h2>Library</h2><span class="mono">'+LIB.length+' entries</span></div><input type="search" id="q" placeholder="Search a word, rule, meaning or root" value="'+esc(LQ)+'" aria-label="Search the library"><div class="card" id="res"></div></div>';
  shell(h);renderRes()}
function renderRes(){var q=lc(LQ.trim()),list;
  if(!q)list=LIB.slice(0,40);else{var a=[],b=[];LIB.forEach(function(c){if(headOf(c).indexOf(q)>=0)a.push(c);else if(searchText(c).indexOf(q)>=0)b.push(c)});list=a.concat(b).slice(0,60)}
  document.getElementById('res').innerHTML=list.length?list.map(function(c){var t=entryTitle(c);return '<details><summary><span>'+esc(cap(t[0]))+'</span><small>'+esc(t[1])+'</small></summary><div style="padding-top:8px">'+entryHTML(c)+'</div></details>'}).join(''):'<span class="muted">No match.</span>'}

function viewStats(){var t=today(),all=counts('all'),acc=S.q?Math.round(S.c/S.q*100):0,days=[],mx=1;
  for(var i=13;i>=0;i--){var l=S.log[t-i],n=l?l.r+l.q:0;days.push(n);mx=Math.max(mx,n)}
  var streak=(S.last===t||S.last===t-1)?S.streak:0;
  var h='<div class="stack"><div class="sec"><h2>Progress</h2></div><div class="kv"><div><span class="mono">Streak</span><b>'+streak+'</b></div><div><span class="mono">Mastered</span><b>'+all.mast+'</b></div><div><span class="mono">Lifetime accuracy</span><b>'+acc+'%</b></div></div>'+
   (S.lt?'<div class="card small">Last test: <b>'+S.lt[0]+' / '+S.lt[1]+'</b> correct. Lifetime accuracy counts every test answer you have ever given.</div>':'')+'<div class="card"><div class="mono" style="margin-bottom:8px">Last 14 days (reviews + test answers)</div><div class="bars" role="img" aria-label="Daily activity, last 14 days">'+days.map(function(n){return '<div class="'+(n?'':'z')+'" style="height:'+Math.max(3,n/mx*100)+'%" title="'+n+'"></div>'}).join('')+'</div><div class="row" style="justify-content:space-between;margin-top:6px"><span class="mono">14 d ago</span><span class="mono">today</span></div></div>';
  if(S.mocks&&S.mocks.length)h+='<div class="card"><div class="mono" style="margin-bottom:6px">Mock scores</div>'+S.mocks.slice(-5).reverse().map(function(m){return '<div class="gh"><span class="muted">'+dayLabel(m.d)+'</span><span><b>'+m.s+' / '+m.max+'</b> <span class="muted small">'+m.c+' right, '+m.w+' wrong</span></span></div>'}).join('')+'</div>';
  ORDER.concat(GORDER.length?['grammar']:[]).concat(RORDER.length?['rules120']:[]).forEach(function(d){var c=counts(d);h+='<div class="card deck"><h3>'+DECKS[d].name+'</h3><div class="mono">'+c.mast+' / '+c.total+'</div><div class="meter"><i class="m" style="width:'+(c.mast/c.total*100)+'%"></i><i class="s" style="width:'+((c.seen-c.mast)/c.total*100)+'%"></i></div><div class="sub" style="grid-column:1/-1">'+c.seen+' started · '+c.mast+' mastered (reviewed correctly 4+ times in a row)</div></div>'});
  h+='<div class="card stack"><div><b>Backup</b><div class="muted small">Progress is saved in this browser. Copy the code to keep a backup or move to another phone.</div></div><textarea id="bk" readonly aria-label="Backup code"></textarea><div class="row"><button class="btn" data-act="copy">Copy code</button><button class="btn" data-act="restore">Restore from pasted code</button></div><div id="bkmsg" class="small muted"></div></div></div>';
  shell(h);var ta=document.getElementById('bk');try{ta.value=btoa(unescape(encodeURIComponent(JSON.stringify(S))))}catch(e){}}

var fmt=function(ms){ms=Math.max(0,ms);var s=Math.ceil(ms/1000),m=Math.floor(s/60);return m+':'+(s%60<10?'0':'')+(s%60)};
function dayLabel(d){try{return new Date(d*864e5).toLocaleDateString('en-IN',{day:'numeric',month:'short',timeZone:'UTC'})}catch(e){return ''}}
function viewMock(){var hist=(S.mocks||[]).slice(-5).reverse();
  var h='<div class="stack"><div class="sec"><h2>SSC-style mock</h2></div><div class="card stack"><div><b>English, '+MOCK_N+' questions, '+MOCK_MIN+' minutes</b><div class="muted small">+2 for each correct answer, −0.5 for each wrong one, 0 for skipped. Maximum '+(2*MOCK_N)+' marks. The test submits itself when the clock reaches zero. You can jump between questions and mark any for review.</div></div>'+
   '<div class="chips">'+MOCKSPEC.map(function(sp){return '<span class="chip">'+sp[0]+' · '+sp[1]+'</span>'}).join('')+'</div>'+
   '<button class="btn primary" data-act="mock" style="min-height:52px;font-size:16px">Start mock</button></div>'+
   (hist.length?'<div class="card"><div class="mono" style="margin-bottom:6px">Recent mocks</div>'+hist.map(function(m){return '<div class="gh"><span class="muted">'+dayLabel(m.d)+'</span><span><b>'+m.s+' / '+m.max+'</b> <span class="muted small">'+m.c+' right, '+m.w+' wrong</span></span></div>'}).join('')+'</div>':'')+'</div>';
  shell(h)}
function viewMockTest(scroll){
  var q=M.qs[M.i],n=M.qs.length,got=M.a.filter(function(x){return x!==null}).length,left=M.end-Date.now();
  var h='<div class="mockhead"><div class="row" style="justify-content:space-between"><span class="mono">Q '+(M.i+1)+' / '+n+' · '+got+' answered</span><span class="clock'+(left<12e4?' low':'')+'" id="clk">'+fmt(left)+'</span></div></div>'+
   '<details class="card" id="palwrap"'+(M.palOpen?' open':'')+'><summary>Question palette <small>'+got+' of '+n+' answered</small></summary><div class="pal">'+M.qs.map(function(_,i){return '<button class="'+(M.a[i]!==null?'ans':'')+(M.mk[i]?' mark':'')+(i===M.i?' cur':'')+'" data-jump="'+i+'" aria-label="Question '+(i+1)+'">'+(i+1)+'</button>'}).join('')+'</div><div class="small muted" style="margin-top:8px">Dark: answered. Yellow: marked for review.</div></details>'+
   '<div class="mono" style="margin-top:14px">'+esc(q.cat)+' · '+esc(q.prompt)+'</div><div class="q'+((q.long||q.sub.length>70)?' long':'')+'"><em>'+esc(q.sub)+'</em></div><div class="opts">'+
   q.opts.map(function(o,i){return '<button class="opt'+(M.a[M.i]===i?' sel':'')+'" data-mopt="'+i+'"><span class="bubble">'+'ABCD'.charAt(i)+'</span><span>'+esc(o)+'</span></button>'}).join('')+'</div>'+
   '<div class="row" style="margin-top:14px"><button class="btn grow" data-act="mprev"'+(M.i?'':' disabled')+'>Previous</button><button class="btn grow" data-act="mclear"'+(M.a[M.i]===null?' disabled':'')+'>Clear</button><button class="btn grow" data-act="mmark">'+(M.mk[M.i]?'Unmark':'Mark for review')+'</button></div>'+
   '<div class="row" style="margin-top:10px"><button class="btn primary grow" data-act="mnext" style="min-height:52px"'+(M.i+1>=n?' disabled':'')+'>Save and next</button></div>'+
   '<div class="row" style="margin-top:18px"><button class="btn grow" data-act="msubmit" style="'+(M.confirm?'border-color:var(--bad);color:var(--bad)':'')+'">'+(M.confirm?'Tap again to submit ('+(n-got)+' unanswered)':'Submit test')+'</button><button class="btn ghost" data-act="exit">Quit</button></div>';
  shell(h,false);if(scroll)window.scrollTo(0,0)}
function mockTick(){clearInterval(mtick);mtick=setInterval(function(){var left=M?M.end-Date.now():0,el=document.getElementById('clk');
  if(el){el.textContent=fmt(left);el.classList.toggle('low',left<12e4)}if(left<=0)submitMock()},500)}
function submitMock(){if(!M||M.done)return;clearInterval(mtick);var n=M.qs.length,cor=0,wr=0,cats={};
  M.qs.forEach(function(q,i){var c=cats[q.cat]=cats[q.cat]||{t:0,a:0,c:0};c.t++;var a=M.a[i];if(a===null)return;c.a++;if(a===q.ans){cor++;c.c++}else{wr++;if(q.id)penalize(q.id)}});
  var marks=cor*2-wr*.5,used=Math.min(MOCK_MIN*60000,Date.now()-M.start);
  M.res={cor:cor,wr:wr,skip:n-cor-wr,marks:marks,max:2*n,used:used,cats:cats};M.done=true;
  S.q+=cor+wr;S.c+=cor;if(cor+wr)logDay('q',cor+wr);S.mocks.push({d:today(),s:marks,max:2*n,c:cor,w:wr});S.mocks=S.mocks.slice(-30);save();render()}
function viewMockResult(){var r=M.res,att=r.cor+r.wr,acc=att?Math.round(r.cor/att*100):0;
  var h='<div class="stack" style="margin-top:20px"><div class="card"><div class="mono">Mock result</div><div class="score">'+r.marks+'<span class="muted" style="font-size:26px"> / '+r.max+'</span></div>'+
   '<div class="kv" style="margin:12px 0"><div><span class="mono">Correct</span><b>'+r.cor+'</b></div><div><span class="mono">Wrong</span><b>'+r.wr+'</b></div><div><span class="mono">Skipped</span><b>'+r.skip+'</b></div></div>'+
   '<p>'+acc+'% accuracy on attempted questions. Time used '+fmt(r.used)+' of '+MOCK_MIN+':00.</p><div class="row"><button class="btn primary" data-act="mock">New mock</button><button class="btn" data-act="exit">Done</button></div></div>'+
   '<div class="card"><div class="mono" style="margin-bottom:6px">By section</div><div class="tblwrap"><table class="tbl"><tr><th>Section</th><th>Right</th><th>Tried</th><th>Of</th></tr>'+
   Object.keys(r.cats).map(function(k){var c=r.cats[k];return '<tr><td>'+esc(k)+'</td><td>'+c.c+'</td><td>'+c.a+'</td><td>'+c.t+'</td></tr>'}).join('')+'</table></div></div>'+
   '<div class="card"><div class="row" style="justify-content:space-between"><div class="mono">Review</div><button class="btn" data-act="mfilter" style="min-height:36px;padding:4px 12px">'+(M.only?'Show all':'Wrong and skipped only')+'</button></div>'+
   M.qs.map(function(q,i){var a=M.a[i];if(M.only&&a===q.ans)return '';
     return '<div class="wrong"><span class="mono">Q'+(i+1)+' · '+esc(q.cat)+' · '+(a===null?'Skipped':a===q.ans?'Correct':'Wrong')+'</span><b>'+esc(q.sub)+'</b><span class="small">Your answer: '+(a===null?'none':esc(q.opts[a]))+'</span><span class="small">Correct: '+esc(q.opts[q.ans])+'</span><span class="small muted">'+q.explain+'</span></div>'}).join('')+'</div></div>';
  shell(h,false);window.scrollTo(0,0)}

function render(){clearInterval(tick);
  if(V.mode==='learn')return viewLearn();if(V.mode==='quiz')return viewQuiz();
  if(V.mode==='mock')return M&&M.done?viewMockResult():viewMockTest(true);
  if(V.tab==='today')viewToday();else if(V.tab==='practice')viewPractice();else if(V.tab==='mock')viewMock();else if(V.tab==='library')viewLibrary();else viewStats()}

function normalize(o){if(!o||typeof o!=='object'||Array.isArray(o)||!o.cards||typeof o.cards!=='object')throw 0;
  var t=today(),int=function(v,lo,hi){v=Math.trunc(+v);return isFinite(v)?Math.max(lo,Math.min(hi,v)):lo};
  var n={cards:{},log:{},streak:int(o.streak,0,3650),last:int(o.last,0,t),q:int(o.q,0,1e6),c:int(o.c,0,1e6),newPer:[5,10,20].indexOf(+o.newPer)>=0?+o.newPer:10};
  Object.keys(o.cards).forEach(function(k){var c=o.cards[k];
    if(Object.prototype.hasOwnProperty.call(byId,k)&&c&&typeof c==='object'&&isFinite(+c.b)&&isFinite(+c.d))n.cards[k]={b:int(c.b,0,5),d:int(c.d,t-3650,t+3650),s:int(c.s,0,1e5)}});
  if(o.log&&typeof o.log==='object')Object.keys(o.log).forEach(function(k){var l=o.log[k];
    if(/^\d{1,6}$/.test(k)&&+k<=t&&+k>=t-3650&&l&&typeof l==='object')n.log[k]={r:int(l.r,0,5000),q:int(l.q,0,5000)}});
  if(Array.isArray(o.lt)&&o.lt.length===2){var q2=int(o.lt[1],1,100),s2=int(o.lt[0],0,q2);n.lt=[s2,q2]}
  n.mocks=Array.isArray(o.mocks)?o.mocks.slice(-30).map(function(m){m=m||{};return{d:int(m.d,0,t),s:Math.max(-100,Math.min(100,+m.s||0)),max:int(m.max,1,200),c:int(m.c,0,200),w:int(m.w,0,200)}}):[];
  if(n.c>n.q)n.c=n.q;return n}
/* ---------- events ---------- */
function startLearn(deck){var q=buildQueue(deck);if(!q.length){V.mode=null;return render()}L={q:q,i:0,flipped:false,done:0,deck:deck};V.mode='learn';render()}
function startQuiz(deck){var list=buildQuiz(deck,V.cnt);if(!list.length)return;Q={list:list,i:0,ans:null,score:0,wrong:[],timed:V.timed,deck:deck};V.mode='quiz';render()}
app.addEventListener('click',function(e){
  var el=e.target.closest('[data-act],[data-tab],[data-opt],[data-mopt],[data-jump],[data-deck],[data-cnt],[data-timed],[data-new]');if(!el)return;
  if(el.dataset.tab){if(V.tab!==el.dataset.tab)V.sub=null;V.tab=el.dataset.tab;V.mode=null;return render()}
  if(el.dataset.opt!==undefined)return answer(+el.dataset.opt);
  if(el.dataset.jump!==undefined){M.i=+el.dataset.jump;M.confirm=false;return viewMockTest(true)}
  if(el.dataset.mopt!==undefined){M.a[M.i]=+el.dataset.mopt;M.confirm=false;return viewMockTest(false)}
  if(el.dataset.new){S.newPer=+el.dataset.new;save();return render()}
  if(el.dataset.cnt){V.cnt=+el.dataset.cnt;return render()}
  if(el.dataset.timed!==undefined&&!el.dataset.act){V.timed=el.dataset.timed==='1';return render()}
  var act=el.dataset.act;
  if(act==='grp'){V.sub=el.dataset.g;return render()}
  if(act==='subback'){V.sub=null;return render()}
  if(!act&&el.dataset.deck){V.deck=el.dataset.deck;return render()}
  if(act==='learn')return startLearn(el.dataset.deck);
  if(act==='quiz'){var qd=el.dataset.deck;if(isG(qd)){V.gtopic=qd.slice(2);qd='gram'}else if(qd==='grammar'){V.gtopic='';qd='gram'}else if(isR(qd)){V.rtopic=qd.slice(3);qd='rules'}else if(qd==='rules120'){V.rtopic='';qd='rules'}V.deck=qd;if(V.mode==='quiz'||V.mode==='learn'){V.mode=null}return startQuiz(qd)}
  if(act==='mock'){M=newMock();V.mode='mock';mockTick();return render()}
  if(act==='mprev'){if(M.i>0)M.i--;M.confirm=false;return viewMockTest(true)}
  if(act==='mnext'){if(M.i<M.qs.length-1)M.i++;M.confirm=false;return viewMockTest(true)}
  if(act==='mclear'){M.a[M.i]=null;M.confirm=false;return viewMockTest(false)}
  if(act==='mmark'){M.mk[M.i]=!M.mk[M.i];M.confirm=false;return viewMockTest(false)}
  if(act==='msubmit'){if(!M.confirm){M.confirm=true;return viewMockTest(false)}return submitMock()}
  if(act==='mfilter'){M.only=!M.only;return viewMockResult()}
  if(act==='exit'){clearInterval(mtick);V.mode=null;L=null;Q=null;M=null;return render()}
  if(act==='flip'){L.flipped=true;return viewLearn()}
  if(act==='know'||act==='again'){var c=L.q[L.i];grade(c.id,act==='know');
    if(act==='again'&&!L.requeued){L.requeued={};}
    if(act==='again'&&!L.requeued[c.id]){L.requeued[c.id]=1;L.q.splice(Math.min(L.i+4,L.q.length),0,c);L.note='"'+(c.w?c.w.w:c.x?c.x.w:c.it?c.it.t:'That card')+'" will come back in 3 cards.'}else L.done++;
    L.i++;L.flipped=false;return viewLearn()}
  if(act==='retryq'){Q.ans=null;Q.retry=true;return viewQuiz()}
  if(act==='next'){Q.i++;Q.ans=null;Q.retry=false;Q.retried=false;return viewQuiz()}
  if(act==='retry'){var w=Q.wrong.slice();Q={list:w,i:0,ans:null,score:0,wrong:[],timed:Q.timed,deck:Q.deck};return viewQuiz()}
  if(act==='copy'){var ta=document.getElementById('bk'),m=document.getElementById('bkmsg');ta.select();
    var ok=function(){m.textContent='Copied. Paste it somewhere safe.'},no=function(){m.textContent='Select the code above and copy it manually.'};
    try{navigator.clipboard.writeText(ta.value).then(ok,no)}catch(x){no()}return}
  if(act==='restore'){var ta2=document.getElementById('bk'),m2=document.getElementById('bkmsg');ta2.readOnly=false;
    if(!ta2.dataset.armed){ta2.dataset.armed='1';ta2.value='';ta2.placeholder='Paste your backup code here, then press Restore again.';ta2.focus();return}
    try{S=normalize(JSON.parse(decodeURIComponent(escape(atob(ta2.value.trim())))));save();m2.textContent='Restored.';setTimeout(function(){render()},600)}catch(x){m2.textContent='That code did not work. Check you pasted all of it.'}return}
});
app.addEventListener('change',function(e){if(e.target.id==='gtopic')V.gtopic=e.target.value});
app.addEventListener('toggle',function(e){if(e.target.id==='palwrap'&&M)M.palOpen=e.target.open},true);
app.addEventListener('input',function(e){if(e.target.id==='q'){LQ=e.target.value;renderRes()}});
document.addEventListener('keydown',function(e){
  if(V.mode==='learn'&&L&&L.i<L.q.length){if(e.key===' '||e.key==='Enter'){if(!L.flipped){e.preventDefault();L.flipped=true;viewLearn()}}
    else if(L.flipped&&e.key==='1'){app.querySelector('.again').click()}else if(L.flipped&&e.key==='2'){app.querySelector('.know').click()}}
  if(V.mode==='quiz'&&Q&&Q.i<Q.list.length){var k='1234'.indexOf(e.key);if(Q.ans===null&&k>=0&&k<Q.list[Q.i].opts.length)answer(k);else if(Q.ans!==null&&(e.key==='Enter'||e.key==='ArrowRight')){Q.i++;Q.ans=null;Q.retry=false;Q.retried=false;viewQuiz()}}});
render();
})();
