package cpu;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Classe do algoritmo de escalonamento Round-Robin.
 * @author MOISÉS CAVALCANTE FERNANDES
 */
public class AlgorithmRR extends Algorithm{
    private final int quantum;
    private /*@ spec_public nullable @*/ final CriarLog1 log1; //@ in Clog1;
    //@ private represents Clog1 <- this.log1;
    private /*@ spec_public nullable @*/ final CriarLog2 log2; //@ in Clog2;
    //@ private represents Clog2 <- this.log2;
    private /*@ spec_public nullable @*/ final CriarLog3 log3; //@ in Clog3;
    //@ private represents Clog3 <- this.log3;
    /**
     * MÃ©todo Construtor da Classe AlgorithmRR.
     * @param pathFile Representa o caminho do arquivo "processos.dat". 
     * @param quantum Representa um valor usado pelo algoritmo para efetuar a substituiÃ§Ã£o de processos na execuÃ§Ã£o.
     */
    public AlgorithmRR(String pathFile, int quantum){
         super(pathFile);
         this.quantum = quantum;
         this.log1 = new CriarLog1("AlgorithmRR");
         this.log2 = new CriarLog2("AlgorithmRR");
         this.log3 = new CriarLog3("AlgorithmRR");
     }
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
        //add mais coisas aqui: 
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
        log1.close();
        log2.close();
        log3.close();
    }
}
