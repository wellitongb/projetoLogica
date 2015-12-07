package cpu;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;

/**
 * Classe do algoritmo de escalonamento Shortest Job First.
 * @author ELISIO BRENO GARCIA CARDOSO
 */
public class AlgorithmSJF extends Algorithm{
	private /*@ spec_public nullable @*/ final CriarLog1 log1; //@ in Clog1;
    //@ private represents Clog1 <- this.log1;
    private /*@ spec_public nullable @*/ final CriarLog2 log2; //@ in Clog2;
    //@ private represents Clog2 <- this.log2;
    private /*@ spec_public nullable @*/ final CriarLog3 log3; //@ in Clog3;
    //@ private represents Clog3 <- this.log3;
    /**
     *Método construtor da classe AlgorithmSJF.
     * @param pathFile Representa o caminho do arquivo processos.dat
     */
    public AlgorithmSJF(String pathFile){
        super(pathFile);
        log1 = new CriarLog1("AlgorithmSJF");
        log2 = new CriarLog2("AlgorithmSJF");
        log3 = new CriarLog3("AlgorithmSJF");
    }

    @Override
    protected void espera() {
        if(super.ProcessoEstadoExecutando != null){
            if((super.ProcessoEstadoExecutando.getNPicos() - 1) > super.ProcessoEstadoExecutando.getPicoAtualIndex()){
                if(super.ProcessoEstadoExecutando.getPicoAtualValue() == super.executionTime){
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
                element.setEstado(Processo.PRONTO);
                element.addLifeTime();
            }
        }
        
        Collections.sort(super.FilaEstadoPronto , new Comparator<Processo>() {
            @Override
            public int compare(Processo o1, Processo o2) {
                if(o1.getPicoAtualValue() > o2.getPicoAtualValue())
                    return 1;
                if(o1.getPicoAtualValue() < o2.getPicoAtualValue())
                    return -1;
                else
                    return 0;
            }
        });
    }

    @Override
    protected void finalizado() {
        if(super.ProcessoEstadoExecutando != null){
            if((super.ProcessoEstadoExecutando.getNPicos() - 1) == super.ProcessoEstadoExecutando.getPicoAtualIndex()){
                if(super.ProcessoEstadoExecutando.getPicoAtualValue() == super.executionTime){
                    super.executionTimeTotal = super.executionTimeTotal + super.executionTime;
                    super.executionTime = 0;
                    super.ProcessoEstadoExecutando.setEstado(Processo.FINALIZADO);
                    super.FilaEstadoFinalizado.add(super.ProcessoEstadoExecutando);
                    this.log1.print(super.ProcessoEstadoExecutando, super.timeSystem);
                    super.ProcessoEstadoExecutando = null;
                }
            }
        }
    }
    
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
     * Método responsável por rodar o algoritmo.
     */
    /*@ also
    @		requires this.log2 != null && this.log3 != null && super.memoryProcess != null && super.FilaEstadoFinalizado != null;
    @		assignable super.timeSystem;
    @		ensures super.timeSystem == \old(super.timeSystem) + super.FilaEstadoFinalizado.size();
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
     * Método responsável por fechar todos os arquivos de log abertos por esse algoritmo.
     */
    @Override
    public /*@ pure @*/ void close(){
        this.log1.close();
        this.log2.close();
        this.log3.close();
    }
}
