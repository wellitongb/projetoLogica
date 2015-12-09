package cpu;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Classe do algoritmo de escalonamento Round-Robin.
 * @author MOISES CAVALCANTE FERNANDES
 */
public class AlgorithmRR extends Algorithm{
    private /*@ spec_public @*/ final int quantum;
    private /*@ spec_public nullable @*/ final CriarLog1 log1; //@ in Clog1;
    //@ private represents Clog1 <- this.log1;
    private /*@ spec_public nullable @*/ final CriarLog2 log2; //@ in Clog2;
    //@ private represents Clog2 <- this.log2;
    private /*@ spec_public nullable @*/ final CriarLog3 log3; //@ in Clog3;
    //@ private represents Clog3 <- this.log3;
    
    //@ public invariant 0 <= quantum;
    /**
     * Metodo Construtor da Classe AlgorithmRR.
     * @param pathFile Representa o caminho do arquivo "processos.dat". 
     * @param quantum Representa um valor usado pelo algoritmo para efetuar a substituicao de processos na execucao.
     */
    /*@	requires pathFile != null;
    @ 	assignable this.log1;
    @	assignable this.log2;
    @	assignable this.log3;
    @	assignable this.quantum;
    @	ensures this.log1 != null && this.log2 !=null && this.log3 !=null && this.quantum == quantum;
    @*/
    public AlgorithmRR(String pathFile, int quantum){
         super(pathFile);
         this.quantum = quantum;
         this.log1 = new CriarLog1("AlgorithmRR");
         this.log2 = new CriarLog2("AlgorithmRR");
         this.log3 = new CriarLog3("AlgorithmRR");
     }
    
    /*@ also
    @			requires super.FilaEstadoEspera != null;
    @			requires super.ProcessoEstadoExecutando != null;
    @			requires (super.ProcessoEstadoExecutando.getNPicos() - 1) > super.ProcessoEstadoExecutando.getPicoAtualIndex();
    @			requires super.ProcessoEstadoExecutando.getPicoAtualValue() == super.executionTime;
    @			requires super.ProcessoEstadoExecutando.getPicoAtualValue() <= quantum;
    @			assignable super.executionTime;
    @			assignable super.ProcessoEstadoExecutando;
    @			assignable super.FilaEstadoEspera; 
    @			ensures super.executionTimeTotal == \old(super.executionTimeTotal) + \old(super.executionTime);
    @			ensures super.executionTime == 0;
    @			ensures super.FilaEstadoEspera.size() == \old(super.FilaEstadoEspera.size() + 1);
    @			ensures super.ProcessoEstadoExecutando == null;
    @		also
   	@			requires true;
   	@			assignable \nothing;
    @*/
    @Override
    protected void espera() {
        if(super.ProcessoEstadoExecutando != null){
            if((super.ProcessoEstadoExecutando.getNPicos() - 1) > super.ProcessoEstadoExecutando.getPicoAtualIndex()){
                if((super.ProcessoEstadoExecutando.getPicoAtualValue() <= quantum) && (super.executionTime == super.ProcessoEstadoExecutando.getPicoAtualValue())){
                    super.executionTimeTotal = super.executionTimeTotal + super.executionTime;
                    super.executionTime = 0;
                    super.ProcessoEstadoExecutando.setEstado(Processo.ESPERA);
                    super.ProcessoEstadoExecutando.addPicoAtualIndex();
                    super.FilaEstadoEspera.add(super.ProcessoEstadoExecutando);
                    super.ProcessoEstadoExecutando = null;
                }
            }
        }
        if(!super.FilaEstadoEspera.isEmpty()){
            for (Processo element : super.FilaEstadoEspera) {
                if(element.getIOserviceTime() > 0)
                    element.addLifeTime();
                element.addIOserviceTime();
            }
        }
    }
    
    /*@ also
    @			requires \same;
    @			assignable super.executionTime;
    @			assignable super.ProcessoEstadoExecutando;
    @			assignable super.FilaEstadoPronto; 
    @			ensures (super.ProcessoEstadoExecutando == null) ==> ((!super.FilaEstadoPronto.isEmpty()) ==> (super.FilaEstadoPronto.size() == \old(super.FilaEstadoPronto.size() - 1) && (super.ProcessoEstadoExecutando != null)));
    @			ensures (super.ProcessoEstadoExecutando != null) ==> ((\old(super.executionTime) > 0) ==> (super.executionTime == \old(super.executionTime + 1)));
    @		also
   	@			requires true;
   	@			assignable \nothing;
    @*/
    @Override
    protected void executar() {
        if(super.ProcessoEstadoExecutando == null){
            if(!super.FilaEstadoPronto.isEmpty()){
                super.ProcessoEstadoExecutando = super.FilaEstadoPronto.remove(0);
                super.ProcessoEstadoExecutando.setEstado(Processo.EXECUTANDO);
            }
        }
        else{
            if(super.executionTime > 0)
                super.ProcessoEstadoExecutando.addLifeTime();
            super.executionTime++;
        }
    }
    
    /*@ also
    @			requires super.FilaEstadoNovo != null && super.FilaEstadoFinalizado != null && super.FilaEstadoEspera != null && super.FilaEstadoPronto != null && super.ProcessoEstadoExecutando != null;
    @			assignable super.nProcessosNoSistema; 
    @			assignable super.nProcessosNovos;
	@			assignable super.FilaEstadoNovo;
	@			assignable super.FilaEstadoFinalizado; 
	@ 			assignable super.FilaEstadoEspera;
	@			assignable super.FilaEstadoPronto; 
	@			assignable super.ProcessoEstadoExecutando;
    @			ensures (super.timeSystem == 0) ==> 
    @					super.FilaEstadoNovo.size() == \old(super.FilaEstadoNovo.size() - 10) &&
    @					super.FilaEstadoPronto.size() == \old(super.FilaEstadoPronto.size() + 10) &&
    @					super.nProcessosNovos == \old(nProcessosNovos - 10) &&
    @					super.nProcessosNoSistema == \old(nProcessosNoSistema + 10);
    @			ensures (super.timeSystem != 0) ==> 
    @					((!super.FilaEstadoFinalizado.isEmpty()) ==> 
    @						(super.nProcessosNovos == \old(super.nProcessosNovos) - (super.nProcessosNoSistema - \old(super.nProcessosNoSistema)))) &&
    @					((\old(super.ProcessoEstadoExecutando.getPicoAtualValue()) > this.quantum && \old(super.executionTime) == this.quantum) ==> 
    @						(super.executionTimeTotal == \old(super.executionTimeTotal) + \old(super.executionTime)) &&
    @						(super.executionTime == 0) &&
    @						(super.FilaEstadoPronto.size() == \old(super.FilaEstadoPronto.size() + 1)) &&
    @						(super.ProcessoEstadoExecutando == null)) &&
    @					((!super.FilaEstadoEspera.isEmpty()) ==> 
    @						(super.FilaEstadoPronto.size() == \old(super.FilaEstadoPronto.size()) + (\old(super.FilaEstadoEspera.size()) - super.FilaEstadoEspera.size())));			
    @		also
   	@			requires true;
   	@			assignable \nothing;
    @*/
    @Override
    protected void pronto() {
        if(super.timeSystem == 0){
            Processo aux;
            for(int i = 0; i < 10; i++){
                aux = super.FilaEstadoNovo.remove(0);
                aux.setEstado(Processo.PRONTO);
                super.FilaEstadoPronto.add(aux);
                super.nProcessosNovos--;
                super.nProcessosNoSistema++;
            }
        }
        else{
            if(!super.FilaEstadoFinalizado.isEmpty()){
                while(10 > (super.nProcessosNoSistema - super.FilaEstadoFinalizado.size()) && !super.FilaEstadoNovo.isEmpty()){
                    super.FilaEstadoPronto.add(super.FilaEstadoNovo.remove(0));
                    super.nProcessosNovos--;
                    super.nProcessosNoSistema++;
               }
            }
            if(super.ProcessoEstadoExecutando != null && super.ProcessoEstadoExecutando.getPicoAtualValue() > quantum && super.executionTime == quantum){
                super.executionTimeTotal = super.executionTimeTotal + super.executionTime;
                super.executionTime = 0;
                super.ProcessoEstadoExecutando.setEstado(Processo.PRONTO);
                super.ProcessoEstadoExecutando.setPicoAtualValue(super.ProcessoEstadoExecutando.getPicoAtualValue() - quantum);
                super.FilaEstadoPronto.add(super.ProcessoEstadoExecutando);
                super.ProcessoEstadoExecutando = null;
            }
            if(!super.FilaEstadoEspera.isEmpty()){
                for (int i = 0; i < super.FilaEstadoEspera.size();i++) {
                    Processo element = super.FilaEstadoEspera.get(i);
                    if(element.getIOserviceTime()%10 == 0){
                        super.FilaEstadoEspera.remove(element);
                        super.FilaEstadoPronto.add(element);
                    }
                }
            }
            for(Processo element : super.FilaEstadoPronto){
                element.setEstado(Processo.NOVO);
                element.addLifeTime();
            }
        }
    }
    
    /*@ also
    @			requires super.FilaEstadoFinalizado != null && super.ProcessoEstadoExecutando != null;
    @			requires (super.ProcessoEstadoExecutando.getNPicos() - 1) == super.ProcessoEstadoExecutando.getPicoAtualIndex();
    @			requires super.ProcessoEstadoExecutando.getPicoAtualValue() == super.executionTime;
    @			assignable super.executionTimeTotal;
    @			assignable super.executionTime;
    @			assignable super.ProcessoEstadoExecutando;
    @			assignable super.FilaEstadoFinalizado; 
    @			ensures super.executionTimeTotal == \old(super.executionTimeTotal) + \old(super.executionTime);
    @			ensures super.executionTime == 0;
    @			ensures super.FilaEstadoFinalizado.size() == \old(super.FilaEstadoFinalizado.size() + 1);
    @			ensures super.ProcessoEstadoExecutando == null;
    @		also
   	@			requires true;
   	@			assignable \nothing;
    @*/
    @Override
    protected void finalizado() {
        if(super.ProcessoEstadoExecutando != null){
            if((super.ProcessoEstadoExecutando.getNPicos() - 1) == super.ProcessoEstadoExecutando.getPicoAtualIndex()){
                if(super.ProcessoEstadoExecutando.getPicoAtualValue() == super.executionTime){
                    super.executionTimeTotal = super.executionTimeTotal + super.executionTime;
                    super.executionTime = 0;
                    super.ProcessoEstadoExecutando.setEstado(Processo.FINALIZADO);
                    this.log1.print(super.ProcessoEstadoExecutando, super.timeSystem);
                    super.FilaEstadoFinalizado.add(super.ProcessoEstadoExecutando);
                    super.ProcessoEstadoExecutando = null;
                }
            }
        }
    }
    
    /*@ also
    @		requires super.FilaEstadoNovo != null && super.nProcessosNovos <= super.nProcessos;
    @		assignable super.FilaEstadoNovo;
    @		assignable super.nProcessosNovos; 
    @		ensures super.FilaEstadoNovo.size() >= \old(super.FilaEstadoNovo.size());
    @		ensures super.nProcessosNovos == super.FilaEstadoNovo.size();
    @		ensures (\forall int i; 0 <= i && i < super.nProcessosNovos; super.FilaEstadoNovo.get(i) != null);
    @*/
    @Override
    protected void novo() {
        if(super.nProcessosNovos <= super.nProcessos){
            for(Processo element: super.memoryProcess){
                if(element.getTempoDeChegada() == super.timeSystem){
                    element.setEstado(Processo.NOVO);
                    super.FilaEstadoNovo.add(element);
                    super.nProcessosNovos++;
                }
            }
        }
        if(super.timeSystem > 0){
            for(Processo element: super.FilaEstadoNovo){
                element.addLifeTime();
            }
        }
    }
    /**
     * Metodo responsavel por rodar o algoritmo.
     */
    /*@ also
    @		requires this.log2 != null && this.log3 != null && super.memoryProcess != null && super.FilaEstadoFinalizado != null;
    @		assignable super.timeSystem;
    @		ensures (super.memoryProcess.size() == super.FilaEstadoFinalizado.size()) ==> super.timeSystem > \old(super.timeSystem);
    @*/
	@Override
    public void run() {
        do{
            novo();
            pronto();
            executar();
            espera();
            finalizado();
            super.timeSystem++;
            this.log2.print(new ArrayList<ArrayList<Processo>>(Arrays.asList(super.FilaEstadoPronto,super.FilaEstadoEspera,super.FilaEstadoFinalizado)), super.timeSystem);
        }while(super.memoryProcess.size() > super.FilaEstadoFinalizado.size());
        this.log3.print(new ArrayList<ArrayList<Processo>>(Arrays.asList(super.FilaEstadoPronto,super.FilaEstadoEspera,super.FilaEstadoFinalizado)), super.timeSystem, super.executionTimeTotal);
    }
    
    /**
     * Metodo responsavel por fechar todos os arquivos de log abertos por esse algoritmo.
     */
    @Override
    public /*@ pure @*/ void close(){
        log1.close();
        log2.close();
        log3.close();
    }
}
